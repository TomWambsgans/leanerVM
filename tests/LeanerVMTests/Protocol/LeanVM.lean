import LeanerVM.Protocol.LeanVM

/-!
# The leanVM front page, locked

Statement locks of `LeanerVM/Protocol/LeanVM.lean`: the verifier for any hash, the deployed
verifier, completeness, knowledge soundness in the random-oracle model, and the numbers, with the
axioms each depends on.
-/

open LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol.LeanIsa LeanVM

example (prog : Program) (input : PublicInput) (proof : LeanVM.Proof) :
    verify prog input proof = Id.run (verifier LeanerVM.Protocol.Blake2sHash.blake2sBytes prog
      input proof) := rfl

example {prog : Program} (input : PublicInput) (hsafe : SentinelSafe prog) {A : Adversary}
    {Q : ℕ} (hA : A.IsTotalQueryBound Q) :
    Pr{let z ← experiment prog input A}[z.1.2 = true ∧
      ¬ ∃ t, extract prog input z.2 z.1.1 = some t ∧ ValidExecution prog input t] ≤
      soundnessError Q :=
  knowledgeSoundness input hsafe hA

example {Q : ℕ} (hQ : Q ≤ 2 ^ 64) : soundnessError Q ≤ (2 : ENNReal)⁻¹ ^ 63 := soundnessError_le hQ

/-- info: 'LeanVM.knowledgeSoundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms knowledgeSoundness

/-- info: 'LeanVM.completeness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms completeness

/--
info: 'LeanVM.completeness_of_execution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms completeness_of_execution
