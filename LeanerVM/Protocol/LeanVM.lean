/-
  LeanerVM.Protocol.LeanVM

  The leanVM verifier and what is proved about it, in one page: the verifier for any hash
  function, the deployed verifier (BLAKE2s), knowledge soundness in the random-oracle model at
  128 bits per query, and completeness.
-/

module

public import LeanerVM.Protocol.EndToEnd.Sound.Theorem
public import LeanerVM.Protocol.EndToEnd.Complete.Small

/-!
# leanVM, end to end

What the repository proves about leanVM's verifier at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, stated over three files: the ISA
(`LeanerVM/Semantics.lean`: `Program`, `PublicInput`, `Trace`, `ValidExecution`), the verifier
(`LeanerVM/Protocol/Verifier.lean`), and this page. Everything else in the repository is proof.

**The verifier.** `verifier H prog input proof` is `python-verifier/verifier.py` at that commit,
transcribed into Lean, for a program `prog`, a public input `input` and a proof, with the hash
function `H : Bytes → m Digest` a parameter in any monad `m`. Two instances:

* `verify`: `H` is BLAKE2s-256 (`m = Id`), the deployed verifier, executable:
  `lake exe leanvm-verify` checks a proof of the Rust prover in well under a second (the field
  and BLAKE2s are swapped for word-level code by proven `@[csimp]` theorems);
* the same `verifier` with `H` a query to a random oracle (`m = OracleComp`), which is what the
  knowledge-soundness theorem is about.

**Knowledge soundness** (`knowledgeSoundness`): for a program whose last instruction is not a
`JUMP` and any adversary making at most `Q` queries to the random oracle, the probability that
the verifier accepts the adversary's proof while the extracted execution (`extract`: the memory
image the proof commits to, run until it halts) is not a valid execution of `prog` on `input` is
at most `soundnessError Q = (Q + 13213) · (2^-128 + 6·(Q + 13213)/2^256)`, which is at most
`2^-63` for `Q ≤ 2^64` (`soundnessError_le`). The `2^-128` is per oracle query: every group of
the protocol's challenges, discounted by the proof of work before it, escapes with probability at
most `2^-128`, certified for every admissible size and rate (`Whir.Params.Deployed`).

**Completeness** (`completeness`): for a valid execution of at most `2^19` steps, with a memory
of at most `2^23` words and a bytecode of at most `2^23` instructions, of a program carrying the
fill blocks the prover pads with, the honest prover's proof is accepted by `verifier H`, for
every hash function `H` whose 17-bit proof-of-work search succeeds within the prover's fuel. The
honest prover (`honestProof`) is a specification, not an implementation.

**Scope and trust.**

* BLAKE2s is modelled as a random oracle.
* The statement is non-adaptive: `prog` and `input` are fixed before the oracle, so it says
  nothing directly about an attacker who chooses the public input after querying the oracle.
* The extractor is information-theoretic, not efficient: a classical choice in the list of
  codewords near the committed word.
* A proof is the Python verifier's format: the scalar stream and one full Merkle path per query.
  The Rust prover ships pruned paths (shared siblings per batch, `MerkleOpenings::Pruned`), which
  the deployed `leanvm_core::cpu::verify` expands into these paths and checks more strictly; that
  expansion is not formalized.
* That `verifier` is the Python and Rust verifiers is test evidence: it is a transcription of the
  Python, it accepts the Rust prover's proofs, and on mutated proofs it gives the Rust verifier's
  verdict every time (`scripts/fuzz-verifier.py`).
* Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace LeanVM

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization
open LeanerVM.Protocol LeanerVM.Protocol.Compile LeanerVM.Protocol.Compile.Rom
open LeanerVM.Protocol.Verifier LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.EndToEnd
open LeanerVM.Protocol.Blake2sHash
open Air.Flat (EnsembleWitness)
open scoped ENNReal

@[expose] public section

/-! ## The verifier -/

/-- A proof: the scalar stream and the Merkle openings. -/
abbrev Proof := Compile.Proof

/-- **The leanVM verifier**, for a hash function `H` in any monad `m`: does `proof` show that
`prog` runs on `input`? -/
def verifier {m : Type → Type} [Monad m] (H : Bytes → m Digest) (prog : Program)
    (input : PublicInput) (proof : Proof) : m Bool :=
  verifyWith H (Front.bytecodeWords prog) (Complete.publicDigest input) proof

/-- **The deployed verifier**: `verifier` with BLAKE2s-256. -/
def verify (prog : Program) (input : PublicInput) (proof : Proof) : Bool :=
  Id.run (verifier blake2sBytes prog input proof)

/-- `verify` is the transcription of the deployed verifier, run with BLAKE2s
(`LeanerVM.Protocol.Verifier.verify`, what `lake exe leanvm-verify` runs). -/
theorem verify_eq (prog : Program) (input : PublicInput) (proof : Proof) :
    verify prog input proof =
      LeanerVM.Protocol.Verifier.verify (Front.bytecodeWords prog) (Complete.publicDigest input)
        proof :=
  rfl

/-! ## Knowledge soundness -/

/-- An adversary: a computation with oracle access to the hash function that outputs a proof. -/
abbrev Adversary : Type := OracleComp HashSpec Proof

/-- **The random-oracle experiment**: the adversary, then the verifier on its proof, both
querying one lazily sampled random oracle. Its outcome is the proof, the verdict, and the
oracle's answers. -/
noncomputable def experiment (prog : Program) (input : PublicInput) (A : Adversary) :=
  Rom.romExperiment A (verifier queryH prog input)

/-- The execution of `prog` on a memory image: the image, run from `(1, 1)` for the least number
of steps after which it halts at `(g^(N − 1), 1)`; `none` if it never does. -/
noncomputable def haltingRun (prog : Program) {κ : ℕ} (image : MemImage κ) : Option (Trace prog) :=
  open Classical in
  if h : ∃ n, run prog image n Regs.initial = some (Regs.final prog) then
    some ⟨κ, image, Nat.find h⟩
  else none

/-- **The extractor**: from the oracle's answers and the proof, the execution the proof commits
to: the memory image of the committed stack (the stack's commitment is read off the answers to
the Merkle queries, and the stack is the codeword of its Johnson list satisfying the constraints,
chosen classically), run until it halts. -/
noncomputable def extract (prog : Program) (input : PublicInput) (answers : HashSpec.QueryCache)
    (proof : Proof) : Option (Trace prog) :=
  (Sound.extractStack prog input answers proof).bind fun x ↦
    let image := imageOf (witnessOf Blake2sFlock.blake2sFlockSpec prog x.1 x.2).data
    haltingRun prog image.2

/-- **The soundness error** of an adversary of `Q` queries: one `2^-128` per query of the
adversary and the verifier (at most `13213`), plus collisions. -/
noncomputable def soundnessError (Q : ℕ) : ℝ≥0∞ :=
  ((Q + 13213 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + ((6 * (Q + 13213) : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- A witness representing a valid execution has its image's halting run, valid. -/
theorem haltingRun_valid {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {t : Trace prog}
    (hrep : AssignmentRepresents w t) (hv : ValidExecution prog input t) :
    ∃ t', haltingRun prog (imageOf w.data).2 = some t' ∧ ValidExecution prog input t' := by
  obtain ⟨κ, image, steps⟩ := t
  obtain ⟨hκ, himage, -⟩ := hrep
  generalize imageOf w.data = p at hκ himage ⊢
  obtain ⟨κ', image'⟩ := p
  dsimp only at hκ himage ⊢
  subst hκ
  obtain rfl : image' = image := funext fun i ↦ himage i i.isLt
  have h : ∃ n, run prog image' n Regs.initial = some (Regs.final prog) := ⟨steps, hv.2⟩
  exact ⟨⟨_, image', Nat.find h⟩, by simp only [haltingRun, h, ↓reduceDIte], hv.1,
    Nat.find_spec h⟩

/-- **Knowledge soundness in the random-oracle model.** For a program whose last instruction is
not a `JUMP`, a public input fixed in advance, and an adversary making at most `Q` queries, the
verifier accepts while the extracted execution is not a valid execution of `prog` on `input` with
probability at most `soundnessError Q`. -/
theorem knowledgeSoundness {prog : Program} (input : PublicInput) (hsafe : SentinelSafe prog)
    {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment prog input A}[z.1.2 = true ∧
      ¬ ∃ t, extract prog input z.2 z.1.1 = some t ∧ ValidExecution prog input t] ≤
      soundnessError Q := by
  have hV : verifier queryH prog input =
      verifierComp (leanVmSeed (Front.bytecodeWords prog) (Complete.publicDigest input))
        (leanVmProgram (Front.bytecodeWords prog) (Complete.publicDigest input)) :=
    funext fun π ↦ (verifierComp_leanVm _ _ π).symm
  have h := Sound.romSound_of_imp _ (Sound.leanVmCert prog input) _ Sound.εLean
    (Sound.leanVmCert_bound prog input) A Q hA leanVmQueryBound (isTotalQueryBound_leanVm _ _)
    (fun π c ↦ ¬ ∃ t, extract prog input c π = some t ∧ ValidExecution prog input t)
    (fun _ _ hv hb ↦ Sound.doomed_of_not_extracted prog input hv fun ⟨s, q, hx, hs, hM⟩ ↦
      hb (by
        obtain ⟨t, hrep, ht⟩ := execution_of_extracted Blake2sFlock.blake2sFlockSpec hsafe hs hM
        obtain ⟨t', ht', hv'⟩ := haltingRun_valid hrep ht
        exact ⟨t', by simp only [extract, hx, Option.bind_some]; exact ht', hv'⟩))
  rw [leanVmQueryBound_eq] at h
  unfold experiment
  rw [hV]
  refine h.trans (le_of_eq ?_)
  rw [soundnessError, failBound]
  rfl

/-- **The numbers**: against `2^64` queries, the soundness error is at most `2^-63`. -/
theorem soundnessError_le {Q : ℕ} (hQ : Q ≤ 2 ^ 64) : soundnessError Q ≤ (2 : ℝ≥0∞)⁻¹ ^ 63 := by
  have h := Sound.leanVm_bound_le [] default hQ
  rw [failBound] at h
  exact (le_of_eq (by rfl)).trans h

/-! ## Completeness -/

/-- **The honest prover**: the proof of the execution `t` with the hash `H`, at the commitment's
inverse rate `2^ρ`, its proof-of-work searches bounded by `fuel`; `none` when the execution does
not fit the deployed parameters or a search fails. A specification: it pads the execution, takes
a witness of leanISA's constraint system representing it (a classical choice), and runs the
honest strategy of every phase through the Fiat–Shamir transform. -/
noncomputable def honestProof (H : Bytes → Digest) (prog : Program) (input : PublicInput)
    (t : Trace prog) (ρ fuel : ℕ) : Option Proof :=
  Complete.honestProofOf H prog input t ρ fuel

/-- **Completeness.** For a valid execution of at most `2^19` steps, with a memory of at most
`2^23` words and a bytecode of at most `2^23` instructions, of a program carrying the fill blocks,
at an inverse rate `2^ρ` with `1 ≤ ρ ≤ 4`, and for every hash function whose 17-bit
proof-of-work search finds a nonce below `fuel`, the honest prover returns a proof, and the
verifier accepts it. -/
theorem completeness {prog : Program} {input : PublicInput} {t : Trace prog}
    (hfill : HasFillBlocks prog) (hv : ValidExecution prog input t) (hsteps : t.steps ≤ 2 ^ 19)
    (hmem : t.κ ≤ 23) (hcode : prog.logSize ≤ 23) {ρ : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4)
    (H : Bytes → Digest) (fuel : ℕ)
    (hpow : ∀ cv, findNonce H Whir.queryGrindingBits cv fuel ≠ none) :
    ∃ proof, honestProof H prog input t ρ fuel = some proof ∧
      verifier (m := Id) H prog input proof = true :=
  Complete.complete_of_small hfill hv ⟨hsteps, hmem, hcode⟩ hρ H fuel fun _ _ _ cv hg ↦
    Sound.grind_bits_eq _ _ hg ▸ hpow cv

/-- **Every proof the honest prover returns is accepted**, for every hash function. -/
theorem honestProof_accepted {prog : Program} {input : PublicInput} {t : Trace prog}
    {ρ fuel : ℕ} (H : Bytes → Digest) {proof : Proof}
    (h : honestProof H prog input t ρ fuel = some proof) :
    verifier (m := Id) H prog input proof = true :=
  Complete.verify_honestProofOf H h

end
end LeanVM
