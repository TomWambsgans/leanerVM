/-
  LeanerVM.Protocol.EndToEnd.Complete.Public

  The honest prover of the verifier program's public-input step: the two memory limbs on the line
  through cells 0 and 1, which pass the check against the public digest and make the three
  memory claims true.
-/

module

public import LeanerVM.Protocol.EndToEnd.Complete.Claims
public import LeanerVM.Protocol.Whir.Complete.Script
public import LeanerVM.Protocol.PublicInput
public import LeanerVM.Protocol.Blake2sHash
import LeanerVM.Protocol.Compile.Rom.Encoding

/-!
# The public input

Step 5 of `verify_execution` (`publicInputPhase`, `python-verifier/verifier.py:1397-1402` at
leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`): sample `r`, read two limbs `c₀, c₁`, require
`c₀ + c₁·y = (1 + r)·h₀ + r·h₁` for the halves `(h₀, h₁)` of the public-input digest, and claim
`c₀, c₁, 0` of the three memory columns at `(r, 0, …, 0)`.

* `publicDigest input`: the digest of a public input, its eight 32-bit words (the low and high
  words of each lane), so that its two halves are the public input's two memory words
  (`digestScalars_publicDigest`); the inverse of the soundness side's reading
  `Front.publicInputOfDigest`.
* `hPub`: the honest prover sends the extensions of `MEM_LO` and `MEM_HI` at `(r, 0, …, 0)`, the
  lines through their cells `0, 1` (`PublicInput.eval₂Mle_linePoint`).
* `follows_publicInputPhase`: on a stack satisfying `M3Holds`, its public lines (`MEM_LO` holds
  `input₀, input₂`, `MEM_HI` holds `input₁, input₃`, `MEM_TOP` holds `0, 0`) make the check pass,
  and the three claims are true claims (`TrueClaim`), the third because `MEM_TOP`'s line is zero.
-/

namespace LeanerVM.Protocol.EndToEnd.Complete

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol.Compile LeanerVM.Protocol.Verifier
open LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.EndToEnd.Front LeanerVM.Protocol.Whir.Complete
open LeanerVM.Protocol.Blake2sHash LeanerVM.Protocol.PublicInput CompPoly CMlPolynomialEval

@[expose] public section

/-! ## The digest of a public input -/

/-- The digest of a public input: the low and high 32-bit words of its four lanes, in order
(`hash_to_scalars`, `merkle.rs:14-36`, read backwards). -/
def publicDigest (input : PublicInput) : Digest :=
  #v[lowWord (input.lanes 0), highWord (input.lanes 0), lowWord (input.lanes 1),
    highWord (input.lanes 1), lowWord (input.lanes 2), highWord (input.lanes 2),
    lowWord (input.lanes 3), highWord (input.lanes 3)]

/-- The digest's two halves are the public input's two memory words. -/
theorem digestScalars_publicDigest (input : PublicInput) :
    digestScalars (publicDigest input) = (input.word0, input.word1) := by
  simp [digestScalars, publicDigest, wordsCell, PublicInput.word0, PublicInput.word1,
    Compile.Rom.ofWords_lowWord_highWord]

/-! ## The honest prover -/

/-- The public point `(r, 0, …, 0)` the program claims the memory columns at. -/
def publicPoint (layout : Verifier.Layout) (r : E) : List E :=
  r :: List.replicate ((layout.placements.getD memory0 default).vars - 1) 0

/-- The public claims the program makes after the challenge `r` and the limbs `c₀, c₁`. -/
def publicClaims (layout : Verifier.Layout) (r c₀ c₁ : E) : List Verifier.ColumnClaim :=
  List.zipWith (fun column value ↦ ⟨column, publicPoint layout r, value⟩)
    [memory0, memory1, memory2] [c₀, c₁, 0]

/-- The true value of memory limb `i` on the line through its cells `0, 1`. -/
def memLine (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (i : Fin 4) (r : E) : E :=
  colEval prog s q (memCol i) (linePoint s.logMem_pos r)

/-- **The honest prover of the public input**: receive `r`, send the true values of `MEM_LO` and
`MEM_HI` on their lines; return the program's claims. -/
def hPub (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) :
    Script (List Verifier.ColumnClaim) :=
  Script.sampleE.bind fun r ↦
    (Script.sendList [memLine prog s q 0 r, memLine prog s q 1 r]).bind fun _ ↦
      .ret (publicClaims (verifierLayout prog s) r (memLine prog s q 0 r) (memLine prog s q 1 r))

/-! ## Completeness -/

/-- The public point at the verifier's layout is the line point of the memory columns. -/
theorem publicPoint_eq (prog : Program) (s : Sizes) (r : E) :
    publicPoint (verifierLayout prog s) r = (linePoint s.logMem_pos r).toList := by
  have hp := placement_committed prog s (memCol 0) (by decide)
  rw [pyCol_memCol] at hp
  have hv : ((verifierLayout prog s).placements.getD memory0 default).vars = s.logMem := by
    rw [show memory0 = ((0 : Fin 4) : ℕ) from rfl, hp]
    rfl
  rw [publicPoint, hv]
  simp [linePoint, Vector.toList_cast, Vector.toList_append]

/-- A memory limb's line value, from its cells `0, 1`. -/
theorem memLine_eq (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (i : Fin 4)
    (r : E) :
    memLine prog s q i r =
      (1 + r) * ofK (((inst prog s).column q (memCol i)).values.get ⟨0, Nat.two_pow_pos _⟩) +
        r * ofK (((inst prog s).column q (memCol i)).values.get
          ⟨1, Nat.one_lt_two_pow s.logMem_pos.ne'⟩) := by
  have h := eval₂Mle_linePoint s.logMem_pos ((inst prog s).column q (memCol i)).values r
  rw [CharTwo.sub_eq_add] at h
  exact h

/-- The program's claim on memory limb `i` at the public point is a true claim, when its value
is the limb's line value. -/
theorem trueClaim_memLine (prog : Program) (s : Sizes) (q : Column (leanIsaμ prog s)) (i : Fin 4)
    (r v : E) (hv : v = memLine prog s q i r) :
    TrueClaim prog s q ⟨i, publicPoint (verifierLayout prog s) r, v⟩ :=
  ⟨memCol i, linePoint s.logMem_pos r, by rw [pyCol_memCol, publicPoint_eq, hv]; rfl⟩

/-- **The honest public-input step.** On a stack satisfying `M3Holds`, the honest limbs pass the
check against the public input's digest, and the three claims are true. -/
theorem follows_publicInputPhase {prog : Program} {s : Sizes} {input : PublicInput}
    {q : Column (leanIsaμ prog s)} (hq : M3Holds (inst prog s) input q) (cs : Commits) :
    Follows (fun cs' a b ↦ cs' = cs ∧ a = b ∧ TrueClaims prog s q b) (hPub prog s q)
      (Verifier.publicInputPhase (verifierLayout prog s) (publicDigest input)) cs := by
  have hlines := hq.2.2.2.1
  have hl : ∀ l ∈ ((inst prog s).publicLines input).toList,
      ((inst prog s).column q l.col).values.get ⟨0, Nat.two_pow_pos _⟩ = l.cell0 ∧
        ((inst prog s).column q l.col).values.get ⟨1, Nat.one_lt_two_pow l.pos.ne'⟩ = l.cell1 :=
    hlines
  have h0 := hl _ (by simp [inst, leanIsaInstance, publicLines] : (⟨memCol 0, input.lanes 0,
    input.lanes 2, true, s.logMem_pos⟩ : PublicLine (shape prog s)) ∈ _)
  have h1 := hl _ (by simp [inst, leanIsaInstance, publicLines] : (⟨memCol 1, input.lanes 1,
    input.lanes 3, true, s.logMem_pos⟩ : PublicLine (shape prog s)) ∈ _)
  have h2 := hl _ (by simp [inst, leanIsaInstance, publicLines] : (⟨memCol 2, 0, 0, false,
    s.logMem_pos⟩ : PublicLine (shape prog s)) ∈ _)
  simp only at h0 h1 h2
  unfold Verifier.publicInputPhase hPub
  simp only [Prog.bind_eq]
  refine Follows.bind (fun cs₁ r r' hr ↦ ?_) _ _ _ (Follows.sampleE_sampleE cs)
  obtain ⟨rfl, rfl⟩ := hr
  rw [show (2 : ℕ) = [memLine prog s q 0 r, memLine prog s q 1 r].length from rfl]
  refine Follows.bind (fun cs₂ _ limbs hl ↦ ?_) _ _ _ (Follows.sendList_readN cs₁ _)
  obtain ⟨rfl, rfl⟩ := hl
  have hcheck : polyEval ([memLine prog s q 0 r, memLine prog s q 1 r] ++ [0]) yE =
      multilinearEval [(digestScalars (publicDigest input)).1,
        (digestScalars (publicDigest input)).2] [r] := by
    rw [digestScalars_publicDigest, memLine_eq, memLine_eq, h0.1, h0.2, h1.1, h1.2]
    have hy : yE = y := by rw [yE, ofLimbs_eq]; simp
    simp only [polyEval, multilinearEval, List.foldl, foldPairs, List.headD, List.cons_append,
      List.nil_append, List.foldr, hy, PublicInput.word0, PublicInput.word1, ofLimbs_eq]
    rw [show ofK (0 : K) = 0 from map_zero (algebraMap K E)]
    ring
  simp only [Prog.require, hcheck, ↓reduceIte, Prog.ret_bind, Prog.pure_eq]
  refine ⟨rfl, rfl, ?_⟩
  intro cl hcl
  simp only [List.cons_append, List.nil_append, List.zipWith_cons_cons,
    List.zipWith_nil_right, List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl | rfl
  · exact trueClaim_memLine prog s q 0 r _ rfl
  · exact trueClaim_memLine prog s q 1 r _ rfl
  · refine trueClaim_memLine prog s q 2 r _ ?_
    rw [memLine_eq, h2.1, h2.2]
    simp

end
end LeanerVM.Protocol.EndToEnd.Complete
