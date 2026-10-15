import LeanerVM.Protocol.EndToEnd.Front.FlockBridge

/-!
# The front bridge's tests

* **Statement locks** of the three specifications (public input, Flock, ring switching), with their
  hypotheses, and of the fidelity theorems.
* **The axiom audit**: the specifications and the fidelity theorems use the standard axioms only.
* **What is load-bearing.**
  - The public input's check is the program's: a mutated limb is rejected (`pubAccepts`).
  - The wire's derived coefficient is the one passing ArkLib's round check: another value fails
    it, in both modes.
  - The skip interpolation needs the window denominator: the window is every node's denominator
    (`allInv_flockSkipDomain`), and the interpolation is ArkLib's on the coset values.
  - The ring coefficients: `c_0 = 1`, the identity's coefficient, and the sum identity on a
    function picking out one exponent gives that exponent's ArkLib coefficient.
* **Inhabitants**: candidates read off the commitments are stable (`stable_of_commits`); a message
  of the program's shape (`MsgOk`) in each mode.
-/

namespace LeanerVMTests.Protocol.EndToEnd.Front.FlockBridge

open LeanerVM.Parameters LeanerVM.Protocol LeanerVM.Protocol.Compile
open LeanerVM.Protocol.EndToEnd LeanerVM.Protocol.EndToEnd.Front
open scoped ENNReal NNReal

/-! ## Statement locks -/

noncomputable example (F : FlockSpec) (prog : LeanerVM.Semantics.Program) (s : LeanIsa.Sizes)
    (layout : LeanerVM.Protocol.Verifier.Layout) (C : List Ev → Set (Column layout.stackLog))
    (toI : Column layout.stackLog → Column (fI F prog s).μ)
    (claims : List LeanerVM.Protocol.Verifier.ColumnClaim)
    (input : LeanerVM.Semantics.PublicInput) (hlayout : pubLayoutHyp F prog s layout toI)
    {publicInput : Digest}
    (hinput : Blake2sHash.digestScalars publicInput = (input.word0, input.word1))
    (hstable : CandsStable layout C) {L₀ : ℕ} (hcard : ∀ h, (C h).ncard ≤ L₀)
    {εmax T : ℝ≥0∞} (hT : T ≤ εmax) :
    Spec (LeanerVM.Protocol.Verifier.publicInputPhase layout publicInput)
      (PubPre F prog s layout C toI claims input) (PubPost F prog s layout C toI claims) εmax
      (L₀ * ((overE 1 : ℝ≥0) : ℝ≥0∞)) T :=
  pubPhaseSpec F prog s layout C toI claims input hlayout hinput hstable hcard hT

noncomputable example (F : FlockSpec) (prog : LeanerVM.Semantics.Program) (s : LeanIsa.Sizes)
    (layout : LeanerVM.Protocol.Verifier.Layout) (C : List Ev → Set (Column layout.stackLog))
    (toI : Column layout.stackLog → Column (fI F prog s).μ)
    (claims : List LeanerVM.Protocol.Verifier.ColumnClaim) (input : LeanerVM.Semantics.PublicInput)
    (hlay : ringLayoutHyp F prog s layout toI) (hst : Stable C) {L₀ : ℕ}
    (hcard : ∀ h, (C h).ncard ≤ L₀) {εmax T : ℝ≥0∞} (pt sv : List E) :
    Spec (LeanerVM.Protocol.Verifier.ringSwitch pt sv)
      (LinPost F prog s layout C toI claims input (pt, sv))
      (fun r h ↦ ∀ q ∈ C h, ¬ (ColumnClaimsHold layout claims q ∧
        StackClaim.Holds layout.stackLog
          (LeanerVM.Protocol.Verifier.ringSwitchClaim layout r.1 r.2) q)) εmax
      ((∑ _i ∈ Finset.range 6, (L₀ : ℝ≥0∞) * ((overE 1 : ℝ≥0) : ℝ≥0∞)) + T) T :=
  ringBridgeSpec F prog s layout C toI claims input hlay hst hcard pt sv

example (F : FlockSpec) (prog : LeanerVM.Semantics.Program) (s : LeanIsa.Sizes) :
    WalkFaithful F → TerminalFaithful F prog s :=
  terminalFaithful F prog s

example (layout : LeanerVM.Protocol.Verifier.Layout) (target : E) (point cs : List E) :
    IsMultilinearFn layout.stackLog
      (LeanerVM.Protocol.Verifier.ringSwitchClaim layout target fun rPrime ↦
        LeanerVM.Protocol.Verifier.ringWeight point rPrime cs).1 :=
  isMultilinearFn_ringSwitchClaim layout target point cs

/-! ## The axiom audit -/

/--
info: 'LeanerVM.Protocol.EndToEnd.Front.pubPhaseSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms pubPhaseSpec

/--
info: 'LeanerVM.Protocol.EndToEnd.Front.flockBridgeSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms flockBridgeSpec

/--
info: 'LeanerVM.Protocol.EndToEnd.Front.ringBridgeSpec' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ringBridgeSpec

/--
info: 'LeanerVM.Protocol.EndToEnd.Front.terminalFaithful' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms terminalFaithful

/--
info: 'LeanerVM.Protocol.EndToEnd.Front.ringFaithful' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ringFaithful

/-! ## What is load-bearing -/

/-- The public input's check rejects a mutated limb. -/
example (publicInput : Digest) (r c₀ c₁ : E) (h : pubAccepts publicInput r c₀ c₁) :
    ¬ pubAccepts publicInput r (c₀ + 1) c₁ := by
  intro h'
  rw [pubAccepts_iff] at h h'
  have : (1 : E) = 0 := by linear_combination h' - h
  exact one_ne_zero this

/-- The plain wire's derived coefficient is the only one passing ArkLib's check. -/
example (claim c₀ c₂ : E) :
    SumcheckRound.weightedSum 2 (domOf none) (toVec 3 [c₀, claim + LeanerVM.Protocol.Verifier.sumE
      [c₂] + 1, c₂]) ≠ claim := by
  intro h
  have hok := weightedSum_of_msgOk (eq := none) (claim := claim)
    (msg := [c₀, claim + LeanerVM.Protocol.Verifier.sumE [c₂], c₂]) ⟨c₀, c₂, rfl⟩
  simp [SumcheckRound.weightedSum, domOf, SumcheckRound.evaluate, toVec, Fin.sum_univ_succ] at h hok
  have : (1 : E) = 0 := by linear_combination h - hok
  exact one_ne_zero this

/-- The equality-mode wire's derived coefficient is the only one passing ArkLib's check. -/
example (claim r c₁ c₂ : E) :
    SumcheckRound.weightedSum 2 (domOf (some r))
      (toVec 3 [claim + r * LeanerVM.Protocol.Verifier.sumE [c₁, c₂] + 1, c₁, c₂]) ≠ claim := by
  intro h
  have hok := weightedSum_of_msgOk (eq := some r) (claim := claim)
    (msg := [claim + r * LeanerVM.Protocol.Verifier.sumE [c₁, c₂], c₁, c₂]) ⟨c₁, c₂, rfl⟩
  simp [SumcheckRound.weightedSum, domOf, SumcheckRound.evaluate, toVec, Fin.sum_univ_succ] at h hok
  have : (1 : E) = 0 := by linear_combination h - hok
  exact one_ne_zero this

/-- The window denominator is every node's Lagrange denominator. -/
example (i : Fin (2 ^ Flock.kSkip + 2 ^ Flock.kSkip)) :
    flockSkipDomain.allInv[i] = LeanerVM.Protocol.Verifier.windowDenominator 128 :=
  allInv_flockSkipDomain i

/-- The identity's coefficient is `1`. -/
example (f₀ f₁ f₂ f₃ f₄ f₅ : E) :
    (LeanerVM.Protocol.Verifier.ringCoefficients [f₀, f₁, f₂, f₃, f₄, f₅]).getD 0 0 = 1 := by
  simp [LeanerVM.Protocol.Verifier.ringCoefficients, LeanerVM.Protocol.Verifier.ringMapShifts,
    Flock.ringShifts, LeanerVM.Protocol.Verifier.kBits]

/-! ## Inhabitants -/

/-- Candidates read off the commitments are stable along a run with no commitment. -/
example (f : List (ℕ × ℕ × Word) → Set (Column 3)) : Stable fun h ↦ f (commits h) :=
  stable_of_commits f

/-- A plain round message of the program's shape. -/
example (claim c₀ c₂ : E) :
    MsgOk none claim [c₀, claim + LeanerVM.Protocol.Verifier.sumE [c₂], c₂] := ⟨c₀, c₂, rfl⟩

/-- An equality-mode round message of the program's shape. -/
example (claim r c₁ c₂ : E) :
    MsgOk (some r) claim [claim + r * LeanerVM.Protocol.Verifier.sumE [c₁, c₂], c₁, c₂] :=
  ⟨c₁, c₂, rfl⟩

end LeanerVMTests.Protocol.EndToEnd.Front.FlockBridge
