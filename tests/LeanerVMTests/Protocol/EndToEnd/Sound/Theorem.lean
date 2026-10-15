import LeanerVM.Protocol.EndToEnd.Sound.Theorem

/-!
# The end-to-end knowledge soundness's tests

* **Statement locks** of the random-oracle theorem of the leanVM verifier, the knowledge statement,
  the execution statement, the numeric bound, and the whole program's specification.
* **The axiom audit**: the theorems use the standard axioms only.
* **What is load-bearing.**
  - The stack's shape is "the stack's commitment is the only one": a second commitment breaks it.
  - The error arithmetic: `2^64/|E|` is within `2^-128`, `2^65/|E|` is not.
-/

namespace LeanerVMTests.Protocol.EndToEnd.Sound.Theorem

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol
open LeanerVM.Protocol.Compile LeanerVM.Protocol.Compile.Rom LeanerVM.Protocol.Verifier
open LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.EndToEnd.Sound LeanerVM.Protocol.EndToEnd.Front
open LeanerVM.Protocol.Blake2sHash LeanerVM.Protocol.Rom
open LeanerVM.Protocol.EndToEnd.Complete (publicDigest)
open OracleComp OracleSpec
open scoped ENNReal

/-! ## Statement locks -/

noncomputable example (prog : Program) (input : PublicInput) :
    Spec (leanVmProgram (bytecodeWords prog) (publicDigest input)) (fun _ ↦ False)
      (fun b _ ↦ b = false) ((2 : ℝ≥0∞)⁻¹ ^ 128) 0 0 :=
  leanVmSpec prog input

example (prog : Program) (input : PublicInput)
    (A : OracleComp HashSpec Proof) (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
        (leanVmProgram (bytecodeWords prog) (publicDigest input)))}[z.1.2 = true ∧
      Doomed (leanVmCert prog input) (leanVmSeed (bytecodeWords prog) (publicDigest input))
        z.1.1 z.2] ≤
      ((QA + 13300 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 +
        failBound (leanVmSeed (bytecodeWords prog) (publicDigest input)) (QA + 13300)) :=
  leanVm_romSound prog input A QA hA

example (prog : Program) (input : PublicInput)
    (A : OracleComp HashSpec Proof) (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
        (leanVmProgram (bytecodeWords prog) (publicDigest input)))}[z.1.2 = true ∧
      ¬ ∃ (s : Sizes) (q : Column (leanIsaμ prog s)),
        extractStack prog input z.2 z.1.1 = some (⟨s, q⟩ : Σ s : Sizes, Column (leanIsaμ prog s)) ∧
        s.Admissible prog ∧
          M3Holds (leanIsaInstance Blake2sFlock.blake2sFlockSpec prog s) input q] ≤
      ((QA + 13300 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 +
        failBound (leanVmSeed (bytecodeWords prog) (publicDigest input)) (QA + 13300)) :=
  leanVm_knowledge prog input A QA hA

example (prog : Program) (input : PublicInput)
    (hwf : WellFormedBytecode prog) (A : OracleComp HashSpec Proof) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
        (leanVmProgram (bytecodeWords prog) (publicDigest input)))}[z.1.2 = true ∧
      ¬ ∃ (s : Sizes) (q : Column (leanIsaμ prog s)),
        extractStack prog input z.2 z.1.1 = some (⟨s, q⟩ : Σ s : Sizes, Column (leanIsaμ prog s)) ∧
        ∃ t, AssignmentRepresents (witnessOf Blake2sFlock.blake2sFlockSpec prog s q) t ∧
          ValidExecution prog input t] ≤
      ((QA + 13300 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 +
        failBound (leanVmSeed (bytecodeWords prog) (publicDigest input)) (QA + 13300)) :=
  leanVm_execution prog input hwf A QA hA

example (bytecode : List K) (publicInput : Digest) (QA : ℕ) (hQ : QA ≤ 2 ^ 64) :
    ((QA + 13300 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 +
      failBound (leanVmSeed bytecode publicInput) (QA + 13300)) ≤ (2 : ℝ≥0∞)⁻¹ ^ 63 :=
  leanVm_bound_le bytecode publicInput hQ

/-! ## The axiom audit -/

/--
info: 'LeanerVM.Protocol.EndToEnd.Sound.leanVm_romSound' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms leanVm_romSound

/--
info: 'LeanerVM.Protocol.EndToEnd.Sound.leanVm_knowledge' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms leanVm_knowledge

/--
info: 'LeanerVM.Protocol.EndToEnd.Sound.leanVm_execution' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms leanVm_execution

/--
info: 'LeanerVM.Protocol.EndToEnd.Sound.leanVm_bound_le' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms leanVm_bound_le

/-! ## What is load-bearing -/

/-- A second commitment breaks the stack's shape. -/
example (μ R ht w : ℕ) (W W' : Word) :
    ¬ StackShape μ R [Ev.commit ht w W, Ev.commit ht w W'] := by
  rintro ⟨hlen, -⟩
  simp [commits] at hlen

/-- `2^64` over `|E|` is within `2^-128`. -/
example : ((2 ^ 64 : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 :=
  le_eps_of_nat le_rfl le_rfl

/-- `2^65` over `|E|` is not. -/
example : ¬ ((2 ^ 65 : ℕ) : ℝ≥0∞) / ((2 ^ 192 : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  rw [inv_pow_eq_div 128 192 (by norm_num), ENNReal.div_le_iff (by simp) (by simp),
    ENNReal.div_mul_cancel (by simp) (by simp), Nat.cast_le]
  norm_num

end LeanerVMTests.Protocol.EndToEnd.Sound.Theorem
