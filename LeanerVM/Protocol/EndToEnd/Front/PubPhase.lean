/-
  LeanerVM.Protocol.EndToEnd.Front.PubPhase

  The deployed public-input phase of the verifier program, specified in the calculus of verifier
  programs from the knowledge soundness of the deployed ArkLib public-input phase over the
  leanISA instance.
-/

module

public import LeanerVM.Protocol.Verifier.Verify
public import LeanerVM.Protocol.EndToEnd.Candidates
public import LeanerVM.Protocol.EndToEnd.Claims
public import LeanerVM.Protocol.EndToEnd.Front.PubShape
public import LeanerVM.Protocol.PublicInput
public import LeanerVM.Protocol.LeanIsa

/-!
# The public-input phase as a specification

Step 5 of `verify_execution` (`publicInputPhase`, `python-verifier/verifier.py:1397-1402` at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`): sample `r`, read two limbs `c₀, c₁`, require
`c₀ + c₁·y = (1 + r)·h₀ + r·h₁` for the halves `(h₀, h₁)` of the public-input digest, and claim
`c₀, c₁, 0` for the three memory columns at `(r, 0, …, 0)`. It is `sampleReadRead` with the check
`pubAccepts` and the claims `pubClaims` (`publicInputPhase_eq`).

**The fidelity check.** On the leanISA instance the deployed ArkLib phase
(`deployedPublicInputPhase`) reads the same transcript (the challenge, then the two sent lines'
values as one message) and checks the same equation (`checkWords`): `pubAccepts` is
`checkWords` when the instance's statement is the digest's (`digestScalars publicInput =
(input.word0, input.word1)`, `publicInputOfDigest`) (`checkWords_iff_pubAccepts`). The ArkLib
phase pools, for the third line (not sent), the value it computes from the statement, the line
through cells `0, 0` of `MEM_TOP`, which is `0` at every challenge (`lineValue_memTop`): the value
the program claims. So the program's three claims are the phase's three line claims
(`claimsFrom_pub`). No mismatch.

**The specification** (`pubPhaseSpec`). Doom quantifies over the candidates `C h₀` bound by the
history (for the leanVM program, the candidates of the level-0 commitment, `Candidates`); `toI`
reads a candidate as a stack of the instance:

* `PubPre`: no candidate satisfies the earlier claims, the public lines and the Flock predicate;
* `PubPost`: no candidate satisfies the earlier claims with the public claims appended and the
  Flock predicate (the reading of `Seam.pub`).

The challenge escapes with average at most `L₀ · 1/|E|` (`pub_escape`) for at most `L₀`
candidates: for each candidate satisfying the earlier claims, the phase's statement whose
received claims are true of it (`trueStmt`) is outside the table seam, and the deployed phase's
round-by-round knowledge soundness (`PublicInput.deployed_rbr`) bounds by `1/|E|` the challenges at
which some message is accepted with a verdict in the public seam; a good completion of the
program's transcript is such a message (`good_imp_state`).

**What the layout must give** (bridge A, `pubLayoutHyp`): a claim of the program on memory
column `j < 3` at the public point `(r, 0, …, 0)` holds of a candidate only if the instance's claim
on `MEM_j` at `linePoint r` holds of its reading `toI`.
-/

namespace LeanerVM.Protocol.EndToEnd.Front

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol.Compile LeanerVM.Protocol.Verifier
open LeanerVM.Protocol.Blake2sHash OracleComp CompPoly CMlPolynomialEval
open scoped ENNReal NNReal

@[expose] public section

/-! ## The program -/

/-- The point of the public claims, `(r, 0, …, 0)` on the memory's variables
(`verifier.py:1401`). -/
def pubPoint (layout : Verifier.Layout) (r : E) : List E :=
  r :: List.replicate ((layout.placements.getD memory0 default).vars - 1) 0

/-- The program's check, `poly_eval([c₀, c₁, 0], Y) = multilinear_eval(halves, [r])`
(`verifier.py:1400`). -/
abbrev pubAccepts (publicInput : Digest) (r c₀ c₁ : E) : Prop :=
  polyEval ([c₀, c₁] ++ [0]) yE =
    multilinearEval [(digestScalars publicInput).1, (digestScalars publicInput).2] [r]

/-- The program's claims: `c₀, c₁, 0` on the three memory columns at the public point
(`verifier.py:1401-1402`). -/
def pubClaims (layout : Verifier.Layout) (r c₀ c₁ : E) : List Verifier.ColumnClaim :=
  List.zipWith (fun column value ↦ ⟨column, pubPoint layout r, value⟩)
    [memory0, memory1, memory2] ([c₀, c₁] ++ [0])

/-- The public-input phase is the sample-read-read shape. -/
theorem publicInputPhase_eq (layout : Verifier.Layout) (publicInput : Digest) :
    Verifier.publicInputPhase layout publicInput =
      sampleReadRead (pubAccepts publicInput) (pubClaims layout) := by
  unfold Verifier.publicInputPhase sampleReadRead
  simp only [Prog.bind_eq, Prog.pure_eq, Prog.sampleE, Prog.readN, Prog.readE, Prog.bind,
    Prog.require]
  congr 1
  funext r
  congr 1
  funext c₀
  congr 1
  funext c₁
  split <;> rfl

/-- The check, computed: `c₀ + c₁·y = (1 + r)·h₀ + r·h₁`. -/
theorem pubAccepts_iff (publicInput : Digest) (r c₀ c₁ : E) :
    pubAccepts publicInput r c₀ c₁ ↔
      c₀ + y * c₁ =
        (1 + r) * (digestScalars publicInput).1 + r * (digestScalars publicInput).2 := by
  have hy : yE = y := by
    rw [yE, ofLimbs_eq]
    simp
  simp only [pubAccepts, polyEval, multilinearEval, List.foldl, foldPairs, List.headD,
    List.cons_append, List.nil_append, List.foldr, hy]
  constructor <;> intro h <;> linear_combination h

/-! ## The statement of the instance -/

/-- The public input a digest gives the instance: the four lanes of its two halves, read as
`K` words of two little-endian `u32` each (`hash_to_scalars`, `merkle.rs:14-36`; the memory's
first two words are the digest's halves). -/
def publicInputOfDigest (d : Digest) : PublicInput :=
  ⟨![ofWords d[0] d[1], ofWords d[2] d[3], ofWords d[4] d[5], ofWords d[6] d[7]]⟩

/-- The digest's halves are the two public words of its public input. -/
theorem digestScalars_eq_words (d : Digest) :
    digestScalars d = ((publicInputOfDigest d).word0, (publicInputOfDigest d).word1) := rfl

/-! ## The fidelity of the check and the claims -/

section Fidelity

variable (F : FlockSpec) (prog : Program) (s : LeanIsa.Sizes)

/-- The two sent lines of the leanISA instance: `MEM_LO` and `MEM_HI`. -/
theorem sentLines (input : PublicInput) :
    ((leanIsaInstance F prog s).publicLines input).toList.filter (·.sent) =
      [⟨LeanIsa.memCol 0, input.lanes 0, input.lanes 2, true, s.logMem_pos⟩,
        ⟨LeanIsa.memCol 1, input.lanes 1, input.lanes 3, true, s.logMem_pos⟩] := rfl

/-- **The deployed check is the program's.** On a message of two values, the ArkLib deployed
phase's check on the words is the program's check, when the statement is the digest's. -/
theorem checkWords_iff_pubAccepts {publicInput : Digest} {input : PublicInput}
    (hinput : digestScalars publicInput = (input.word0, input.word1))
    (t : TableOut (leanIsaInstance F prog s)) (r c₀ c₁ : E) :
    PublicInput.checkWords (leanIsaInstance F prog s) (input, t) r [c₀, c₁] = true ↔
      pubAccepts publicInput r c₀ c₁ := by
  rw [pubAccepts_iff, hinput]
  unfold PublicInput.checkWords
  rw [sentLines]
  simp only [decide_eq_true_eq, PublicInput.word0, PublicInput.word1]

/-- The deployed phase accepts the program's message exactly where the program does: the length
is the number of sent lines, two. -/
theorem accepts_iff_pubAccepts {publicInput : Digest} {input : PublicInput}
    (hinput : digestScalars publicInput = (input.word0, input.word1))
    (t : TableOut (leanIsaInstance F prog s)) (r c₀ c₁ : E) :
    PublicInput.accepts (leanIsaInstance F prog s) (PublicInput.checkWords _) (input, t) r
      [c₀, c₁] = true ↔ pubAccepts publicInput r c₀ c₁ := by
  rw [← checkWords_iff_pubAccepts F prog s hinput t r c₀ c₁]
  unfold PublicInput.accepts
  rw [Bool.and_eq_true, decide_eq_true_iff]
  exact ⟨And.right, fun h ↦ ⟨rfl, h⟩⟩

/-- **The top limb's pooled value is zero.** The ArkLib phase pools, for the third line (not
sent), the value it computes: the line through the statement's cells `0, 0` of `MEM_TOP`, which is
`0` at every challenge, the value the program claims. -/
theorem lineValue_memTop (input : PublicInput) (r : E) :
    PublicInput.lineValue (leanIsaInstance F prog s) r
      ((leanIsaInstance F prog s).publicLines input)[2] = 0 := by
  show (1 + r) * ofK 0 + r * ofK 0 = 0
  simp

/-- The claims the deployed phase pools from the message `[c₀, c₁]`: `c₀, c₁` on `MEM_LO, MEM_HI`
and `0` on `MEM_TOP`, all at `linePoint r`. -/
theorem claimsFrom_pub (input : PublicInput) (r c₀ c₁ : E)
    (h : [c₀, c₁].length =
      PublicInput.sentCount (leanIsaInstance F prog s)
        ((leanIsaInstance F prog s).publicLines input))
    (j : Fin 3) :
    (PublicInput.claimsFrom (leanIsaInstance F prog s) r
      ((leanIsaInstance F prog s).publicLines input) [c₀, c₁] h)[j] =
      ⟨LeanIsa.memCol j.castSucc, PublicInput.linePoint s.logMem_pos r, [c₀, c₁, 0][j]⟩ := by
  fin_cases j
  all_goals
    simp only [PublicInput.claimsFrom, PublicInput.claimsWith, Fin.getElem_fin,
      Vector.getElem_ofFn]
  · rfl
  · rfl
  · show (⟨LeanIsa.memCol 2, PublicInput.linePoint s.logMem_pos r,
      PublicInput.lineValue (leanIsaInstance F prog s) r
        ((leanIsaInstance F prog s).publicLines input)[2]⟩ :
          Protocol.ColumnClaim (leanIsaInstance F prog s)) = _
    rw [lineValue_memTop]
    rfl

end Fidelity

/-! ## Pre, post and the layout -/

section Spec

variable (F : FlockSpec) (prog : Program) (s : LeanIsa.Sizes) (layout : Verifier.Layout)
  (C : List Ev → Set (Column layout.stackLog))
  (toI : Column layout.stackLog → Column (leanIsaInstance F prog s).μ)
  (claims : List Verifier.ColumnClaim) (input : PublicInput)

/-- **The public-input phase's precondition**: no candidate satisfies the earlier claims, the public
lines and the Flock predicate. -/
def PubPre (h : List Ev) : Prop :=
  ∀ q ∈ C h, ¬ (ColumnClaimsHold layout claims q ∧
    (leanIsaInstance F prog s).PublicLinesHold input (toI q) ∧
      (leanIsaInstance F prog s).aux (toI q))

/-- **The public-input phase's postcondition** (the reading of `Seam.pub`): no candidate satisfies
the earlier claims with the public claims appended and the Flock predicate. -/
def PubPost (publicClaims : List Verifier.ColumnClaim) (h : List Ev) : Prop :=
  ∀ q ∈ C h, ¬ (ColumnClaimsHold layout (claims ++ publicClaims) q ∧
    (leanIsaInstance F prog s).aux (toI q))

/-- **What the public-input phase needs of the layout** (bridge A): the program's claim on memory
column `j < 3` at the public point holds of a candidate only if the instance's claim on `MEM_j` at
`(r, 0, …, 0)` holds of its reading. -/
def pubLayoutHyp : Prop :=
  ∀ (j : Fin 3) (r v : E) (q : Column layout.stackLog),
    StackClaim.Holds layout.stackLog
        ((⟨j.val, pubPoint layout r, v⟩ : Verifier.ColumnClaim).onStack layout) q →
      Protocol.ColumnClaim.Holds (toI q)
        (⟨LeanIsa.memCol j.castSucc, PublicInput.linePoint s.logMem_pos r, v⟩ :
          Protocol.ColumnClaim (leanIsaInstance F prog s))

/-- A good completion of the program's transcript: the program accepts, and some candidate satisfies
the earlier claims, the public claims and the Flock predicate. -/
def PubGood (publicInput : Digest) (h₀ : List Ev) (r c₀ c₁ : E) : Prop :=
  pubAccepts publicInput r c₀ c₁ ∧ ∃ q ∈ C h₀,
    ColumnClaimsHold layout (claims ++ pubClaims layout r c₀ c₁) q ∧
      (leanIsaInstance F prog s).aux (toI q)

/-! ## The ArkLib statement of a candidate -/

/-- A claim true of a stack: `MEM_LO` at the origin, at its value there. -/
def trueClaim (q : Column (leanIsaInstance F prog s).μ) :
    Protocol.ColumnClaim (leanIsaInstance F prog s) :=
  ⟨LeanIsa.memCol 0, Vector.replicate _ 0,
    eval₂Mle ((leanIsaInstance F prog s).column q (LeanIsa.memCol 0)).values (algebraMap K E)
      (Vector.replicate _ 0)⟩

/-- The statement the phase starts from for a candidate: the public input, and received claims
all true of it. The phase's relations read the received claims only as a conjunct, which the
program's own claims replace. -/
def trueStmt (q : Column (leanIsaInstance F prog s).μ) :
    (leanIsaInstance F prog s).Stmt × TableOut (leanIsaInstance F prog s) :=
  (input, ⟨Vector.replicate _ (trueClaim F prog s q)⟩)

/-- The stack as the phase's oracle. -/
def stackOracle (q : Column (leanIsaInstance F prog s).μ) :
    ∀ i, TheOracle (leanIsaInstance F prog s) i := fun _ ↦ q

/-- A candidate satisfying the earlier claims but not the public lines and the Flock predicate is,
with its true statement, outside the table seam. -/
theorem trueStmt_not_table (q : Column (leanIsaInstance F prog s).μ)
    (h : ¬ ((leanIsaInstance F prog s).PublicLinesHold input q ∧
      (leanIsaInstance F prog s).aux q)) :
    ((trueStmt F prog s input q, stackOracle F prog s q), ()) ∉
      Seam.table (leanIsaInstance F prog s) := by
  rintro ⟨-, hl, ha⟩
  exact h ⟨hl, ha⟩

/-- **A good completion is in the deployed phase's state after the challenge.** If the program
accepts `c₀, c₁` at `r` and the candidate satisfies the public claims and the Flock predicate, the
message `[c₀, c₁]` is accepted by the deployed phase with a verdict in the public seam. -/
theorem good_imp_state (hlayout : pubLayoutHyp F prog s layout toI)
    {publicInput : Digest} (hinput : digestScalars publicInput = (input.word0, input.word1))
    {q : Column layout.stackLog} {r c₀ c₁ : E} (hacc : pubAccepts publicInput r c₀ c₁)
    (hcl : ColumnClaimsHold layout (pubClaims layout r c₀ c₁) q)
    (haux : (leanIsaInstance F prog s).aux (toI q)) :
    ∃ cs, PublicInput.accepts (leanIsaInstance F prog s) (PublicInput.checkWords _)
        (trueStmt F prog s input (toI q)) r cs = true ∧
      ((PublicInput.verdict (leanIsaInstance F prog s) (PublicInput.pooledFrom _)
        (trueStmt F prog s input (toI q)) r cs, stackOracle F prog s (toI q)), ()) ∈
          Seam.pub (leanIsaInstance F prog s) := by
  have hacc' := (accepts_iff_pubAccepts F prog s hinput
    (trueStmt F prog s input (toI q)).2 r c₀ c₁).mpr hacc
  refine ⟨[c₀, c₁], hacc', ?_, haux⟩
  have hlen : [c₀, c₁].length = PublicInput.sentCount (leanIsaInstance F prog s)
      ((leanIsaInstance F prog s).publicLines input) := rfl
  have hv : PublicInput.verdict (leanIsaInstance F prog s) (PublicInput.pooledFrom _)
      (trueStmt F prog s input (toI q)) r [c₀, c₁] =
        PublicInput.pooledFrom _ (trueStmt F prog s input (toI q)) r [c₀, c₁] hlen :=
      dite_eq_left hlen
  rw [hv]
  intro c hc
  simp only [PublicInput.pooledFrom, trueStmt, Vector.toList_append, List.mem_append,
    Vector.toList_replicate, List.mem_replicate] at hc
  rcases hc with ⟨-, rfl⟩ | hc
  · rfl
  · obtain ⟨j, rfl⟩ : ∃ j : Fin 3, (PublicInput.claimsFrom (leanIsaInstance F prog s) r
        ((leanIsaInstance F prog s).publicLines input) [c₀, c₁] hlen)[j] = c := by
      obtain ⟨j, hj, hjc⟩ := List.mem_iff_getElem.mp hc
      exact ⟨⟨j, by simpa using hj⟩, by simpa using hjc⟩
    rw [claimsFrom_pub F prog s input r c₀ c₁ hlen j]
    refine hlayout j r _ q (hcl _ ?_)
    fin_cases j <;> simp [pubClaims, memory0, memory1, memory2]

/-! ## The escape -/

/-- **The challenge's escape.** Under `PubPre`, the average over the challenge of "some completion
is good" is at most `L₀ / |E|`, `L₀` bounding the number of candidates: per candidate, the deployed
phase's round-by-round knowledge soundness at `pubError = 1/|E|`, and the union bound. -/
theorem pub_escape (hlayout : pubLayoutHyp F prog s layout toI)
    {publicInput : Digest} (hinput : digestScalars publicInput = (input.word0, input.word1))
    {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀) {h₀ : List Ev}
    (hpre : PubPre F prog s layout C toI claims input h₀) :
    avgE (fun r ↦ indE (∃ c₀ c₁, PubGood F prog s layout C toI claims publicInput h₀ r c₀ c₁)) ≤
      L₀ * ((overE 1 : ℝ≥0) : ℝ≥0∞) := by
  have := finite_column layout.stackLog
  have hfin : (C h₀).Finite := Set.toFinite _
  let P : Column layout.stackLog → E → Prop := fun q r ↦ ColumnClaimsHold layout claims q ∧
    ∃ cs, PublicInput.accepts (leanIsaInstance F prog s) (PublicInput.checkWords _)
        (trueStmt F prog s input (toI q)) r cs = true ∧
      ((PublicInput.verdict (leanIsaInstance F prog s) (PublicInput.pooledFrom _)
        (trueStmt F prog s input (toI q)) r cs, stackOracle F prog s (toI q)), ()) ∈
          Seam.pub (leanIsaInstance F prog s)
  refine (avgE_mono fun r ↦ indE_mono ?_).trans
    (avgE_indE_exists_le hfin (hcard h₀) (P := P) fun q hq ↦ ?_)
  · rintro ⟨c₀, c₁, hacc, q, hq, hcl, haux⟩
    refine ⟨q, hq, fun c hc ↦ hcl c (List.mem_append_left _ hc), ?_⟩
    exact good_imp_state F prog s layout toI input hlayout hinput hacc
      (fun c hc ↦ hcl c (List.mem_append_right _ hc)) haux
  · by_cases hcl : ColumnClaimsHold layout claims q
    · have hnot := trueStmt_not_table F prog s input (toI q)
        fun h ↦ hpre q hq ⟨hcl, h⟩
      refine (avgE_mono fun r ↦ indE_mono fun hP ↦ hP.2).trans ?_
      rw [avgE_indE_eq_prEvent]
      refine le_trans (prEvent_mono _ _ _ fun r hr ↦ ⟨(), hnot, hr⟩)
        (PublicInput.deployed_rbr (leanIsaInstance F prog s) (pure ())
          (fun x ↦ x.elim) (trueStmt F prog s input (toI q), stackOracle F prog s (toI q))
          ⟨0, rfl⟩ fun i ↦ Fin.elim0 i)
    · refine (avgE_mono fun r ↦ indE_mono (q := False) fun hP ↦ absurd hP.1 hcl).trans ?_
      refine (avgE_le_of_le fun r ↦ (indE_of_not not_false).le).trans ?_
      exact zero_le

/-! ## The specification -/

/-- The candidates a history binds do not change along a run with no commitment. -/
def CandsStable : Prop := ∀ h₀ l, commits l = [] → C (h₀ ++ l) = C h₀

/-- **The public-input phase's specification.** The deployed program's public-input phase, from
`PubPre` to `PubPost`, with lead `L₀ / |E|` (`L₀` bounding the number of candidates, `1/|E|` the
slot's error `pubError`) and any allowance `T ≤ εmax`, given the layout's reading of the memory
claims (`pubLayoutHyp`), the instance's statement read off the digest, and candidates stable
along the phase. -/
noncomputable def pubPhaseSpec (hlayout : pubLayoutHyp F prog s layout toI)
    {publicInput : Digest} (hinput : digestScalars publicInput = (input.word0, input.word1))
    (hstable : CandsStable layout C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀)
    {εmax T : ℝ≥0∞} (hT : T ≤ εmax) :
    Spec (Verifier.publicInputPhase layout publicInput) (PubPre F prog s layout C toI claims input)
      (PubPost F prog s layout C toI claims) εmax (L₀ * ((overE 1 : ℝ≥0) : ℝ≥0∞)) T :=
  (publicInputPhase_eq layout publicInput) ▸
    sampleReadReadSpec (pubAccepts publicInput) (pubClaims layout)
      (PubGood F prog s layout C toI claims publicInput)
      (fun h₀ hpre ↦ pub_escape F prog s layout C toI claims input hlayout hinput hcard hpre)
      (fun h₀ r c₀ c₁ hacc hgood q hq hq' ↦ by
        rw [hstable h₀ _ rfl] at hq
        exact hgood ⟨hacc, q, hq, hq'⟩)
      hT

end Spec

end
end LeanerVM.Protocol.EndToEnd.Front
