/-
  LeanerVM.Protocol.LeanVM

  The leanVM verifier and what is proved about it, in one page: the verifier for any hash
  function, the deployed verifier (BLAKE2s), the honest prover, completeness, and knowledge
  soundness in the random-oracle model at 128 bits per query.
-/

module

public import LeanerVM.Protocol.EndToEnd.Sound.Theorem
public import LeanerVM.Protocol.EndToEnd.Completeness

/-!
# leanVM, end to end

This page states what the repository proves about leanVM's verifier at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`. Everything else in the repository is the proof.

**The verifier.** `verifier H prog input proof` is the verifier of `python-verifier/verifier.py`
at that commit, transcribed into Lean (`LeanerVM.Protocol.Verifier`), for a program `prog`, a
public input `input` and a proof, with the hash function `H : Bytes → m Digest` a parameter in
any monad `m`. Two instances:

* `verify`: `H` is BLAKE2s-256 (`m = Id`), the deployed verifier, executable:
  `lake exe leanvm-verify` checks a proof of the Rust prover in well under a second (the field
  and BLAKE2s are swapped for word-level code by proven `@[csimp]` theorems);
* the same `verifier` with `H` a query to a random oracle (`m = OracleComp`), which is what the
  knowledge-soundness theorem is about.

**Completeness** (`completeness`): if `w` satisfies leanISA's constraint system for `prog` on
`input` (`SatisfiedBy`, e.g. from a valid execution, `completeness_of_execution`), the honest
prover's proof is accepted by `verifier H`, for every hash function `H`. The honest prover is a
specification (`honestProof`); it fails only when a proof-of-work search finds no nonce below
its fuel.

**Knowledge soundness** (`knowledgeSoundness`): for well-formed bytecode and any adversary
making at most `Q` queries to the random oracle, the probability that the verifier accepts the
adversary's proof while the extractor (`extract`, reading the oracle's answers) does not return
a witness representing a valid execution of `prog` on `input` is at most
`soundnessError Q = (Q + 13213) · (2^-128 + 6·(Q + 13213)/2^256)`, which is at most `2^-63` for
`Q ≤ 2^64` (`soundnessError_le`). The `2^-128` is per oracle query: every group of the
protocol's challenges, discounted by the proof of work before it, escapes with probability at
most `2^-128`, certified for every admissible size and rate (`Whir.Params.Deployed`).

**Trust.** BLAKE2s is modelled as a random oracle. The statement is non-adaptive (`prog` and
`input` are fixed before the oracle). That `verifier` is the deployed verifier is test evidence:
it is a transcription of the Python, it accepts the Rust prover's proofs, and on 7500 mutated
proofs it gives the deployed Rust verifier's verdict every time (`scripts/fuzz-verifier.py`). The
extractor is a classical choice in the list of codewords near the committed word. Every theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`.
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

/-! ## Completeness -/

/-- **The honest prover**: the proof of a witness `w` at sizes `s` and rate `ρ`, with the hash `H`;
`none` only when a proof-of-work search finds no nonce below `fuel`. A specification. -/
noncomputable def honestProof (H : Bytes → Digest) (prog : Program) (input : PublicInput)
    (w : EnsembleWitness (leanIsaEnsemble prog)) (s : Sizes) (ρ fuel : ℕ) : Option Proof :=
  Compile.prove H (leanVmProgram (Front.bytecodeWords prog) (Complete.publicDigest input))
    (Complete.leanVmProver prog s ρ (stackOf Blake2sFlock.blake2sFlockSpec prog s w))
    (Id.run (seedWith H (Front.bytecodeWords prog) (Complete.publicDigest input))) fuel

/-- **Completeness.** If `w` satisfies leanISA's constraint system for `prog` on `input`, at
admissible sizes `s` and a valid rate `ρ`, the honest proof is accepted, for every hash
function. -/
theorem completeness {prog : Program} {input : PublicInput}
    {w : EnsembleWitness (leanIsaEnsemble prog)} {s : Sizes} {ρ : ℕ}
    (hw : SatisfiedBy prog input w) (hs : Sizes.ofWitness w = some s) (hadm : s.Admissible prog)
    (hρ : validRate ρ) (H : Bytes → Digest) {fuel : ℕ} {proof : Proof}
    (hproof : honestProof H prog input w s ρ fuel = some proof) :
    verifier (m := Id) H prog input proof = true := by
  have hq := m3Holds_stackOf (F := Blake2sFlock.blake2sFlockSpec) hw hs
  have hrun := Complete.runI_leanVmProgram hadm hρ hq Front.walkFaithful_blake2sFlockSpec
  have h := runProof_prove H _ _ _ fuel (fun chal ↦ (hrun chal).1) (fun chal ↦ (hrun chal).2)
    hproof
  exact h

/-- **Completeness from an execution.** A valid execution of well-formed bytecode that fits has
a padded valid execution and a witness representing it; at admissible sizes and a valid rate,
the honest proof of that witness is accepted, for every hash function. -/
theorem completeness_of_execution {prog : Program} {input : PublicInput} {t : Trace prog}
    (hwf : WellFormedBytecode prog) (hv : ValidExecution prog input t) (hfit : t.Fits) :
    ∃ t', t'.PaddedFrom t ∧ ValidExecution prog input t' ∧
      ∃ w s, AssignmentRepresents w t' ∧ Sizes.ofWitness w = some s ∧
        ∀ ρ, s.Admissible prog → validRate ρ → ∀ (H : Bytes → Digest) fuel proof,
          honestProof H prog input w s ρ fuel = some proof →
            verifier (m := Id) H prog input proof = true := by
  obtain ⟨t', ht', hv', w, hw, hrep⟩ := constraintCompleteness hwf hv hfit
  obtain ⟨s, hs⟩ := sizes_of_satisfiedBy hw
  exact ⟨t', ht', hv', w, s, hrep, hs, fun _ hadm hρ H _ _ h ↦ completeness hw hs hadm hρ H h⟩

/-! ## Knowledge soundness -/

/-- An adversary: a computation with oracle access to the hash function that outputs a proof. -/
abbrev Adversary : Type := OracleComp HashSpec Proof

/-- **The random-oracle experiment**: the adversary, then the verifier on its proof, both
querying one lazily sampled random oracle. Its outcome is the proof, the verdict, and the
oracle's answers. -/
noncomputable def experiment (prog : Program) (input : PublicInput) (A : Adversary) :=
  Rom.romExperiment A (verifier queryH prog input)

/-- **The extractor**: from the oracle's answers and the proof, the witness of the committed
stack (the committed word is read off the answers to the Merkle queries; the stack is a codeword
of its Johnson list satisfying the relation, chosen classically). -/
noncomputable def extract (prog : Program) (input : PublicInput) (answers : HashSpec.QueryCache)
    (proof : Proof) : Option (EnsembleWitness (leanIsaEnsemble prog)) :=
  (Sound.extractStack prog input answers proof).map fun x ↦
    witnessOf Blake2sFlock.blake2sFlockSpec prog x.1 x.2

/-- **The soundness error** of an adversary of `Q` queries: one `2^-128` per query of the
adversary and the verifier (at most `13213`), plus collisions. -/
noncomputable def soundnessError (Q : ℕ) : ℝ≥0∞ :=
  ((Q + 13213 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 + ((6 * (Q + 13213) : ℕ) : ℝ≥0∞) / 2 ^ 256)

/-- **Knowledge soundness in the random-oracle model.** For well-formed bytecode and an adversary
making at most `Q` queries, the verifier accepts while the extracted witness represents no valid
execution of `prog` on `input` with probability at most `soundnessError Q`. -/
theorem knowledgeSoundness {prog : Program} (input : PublicInput) (hwf : WellFormedBytecode prog)
    {A : Adversary} {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment prog input A}[z.1.2 = true ∧
      ¬ ∃ w t, extract prog input z.2 z.1.1 = some w ∧
        AssignmentRepresents w t ∧ ValidExecution prog input t] ≤ soundnessError Q := by
  have hV : verifier queryH prog input =
      verifierComp (leanVmSeed (Front.bytecodeWords prog) (Complete.publicDigest input))
        (leanVmProgram (Front.bytecodeWords prog) (Complete.publicDigest input)) :=
    funext fun π ↦ (verifierComp_leanVm _ _ π).symm
  have h := Sound.romSound_of_imp _ (Sound.leanVmCert prog input) _ Sound.εLean
    (Sound.leanVmCert_bound prog input) A Q hA leanVmQueryBound (isTotalQueryBound_leanVm _ _)
    (fun π c ↦ ¬ ∃ w t, extract prog input c π = some w ∧
      AssignmentRepresents w t ∧ ValidExecution prog input t)
    (fun _ _ hv hb ↦ Sound.doomed_of_not_extracted prog input hv fun ⟨s, q, hx, hs, hM⟩ ↦
      hb (by
        obtain ⟨t, ht⟩ := execution_of_extracted Blake2sFlock.blake2sFlockSpec hwf hs hM
        exact ⟨_, t, by simp [extract, hx], ht⟩))
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

end
end LeanVM
