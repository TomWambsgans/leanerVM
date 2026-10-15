/-
  LeanerVM.Protocol.EndToEnd.Front.PubShape

  A specification, in the calculus of verifier programs, of a sub-program that samples one
  challenge, reads two scalars and then returns or rejects: the shape of the public-input
  phase.
-/

module

public import LeanerVM.Protocol.Compile.Spec
public import LeanerVM.Protocol.EndToEnd.Front.PubEscape

/-!
# Sample, read, read

`sampleReadRead A B` is the program `r ← sample; c₀ ← read; c₁ ← read; if A r c₀ c₁ then
return B r c₀ c₁ else reject`, the shape of the deployed public-input phase
(`LeanerVM.Protocol.Verifier.publicInputPhase`, `verifier.py:1397-1402` at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`).

`sampleReadReadSpec` specifies it from a predicate `Good h₀ r c₀ c₁`, "some candidate the history
`h₀` binds is still alive after the challenge `r` and the values `c₀, c₁`". Doom is `Pre` at the
start and, after each step, that no completion of the transcript so far is good: the prover's
reads keep it by definition, the challenge escapes it with the average of the indicator of "some
completion is good", which the caller bounds (`hesc`), and at a return in doom the caller's
postcondition holds of the returned value (`hpost`). The lead is the caller's bound `L`; the
follower's allowance `T` is charged at the return, after the last read, so `T ≤ εmax`.
-/

namespace LeanerVM.Protocol.EndToEnd.Front

open LeanerVM.Parameters LeanerVM.Protocol.Compile
open scoped ENNReal

@[expose] public section

variable {β : Type}

/-- The program `r ← sample; c₀ ← read; c₁ ← read; if A r c₀ c₁ then return B r c₀ c₁ else
reject`. -/
def sampleReadRead (A : E → E → E → Prop) [∀ r c₀ c₁, Decidable (A r c₀ c₁)]
    (B : E → E → E → β) : Prog β :=
  Prog.sample fun r ↦ Prog.read fun c₀ ↦ Prog.read fun c₁ ↦
    if A r c₀ c₁ then Prog.ret (B r c₀ c₁) else Prog.fail

section Shape

variable (A : E → E → E → Prop) [∀ r c₀ c₁, Decidable (A r c₀ c₁)] (B : E → E → E → β)

/-- The node after the challenge. -/
theorem sampleReadRead_after_one (r : E) :
    (sampleReadRead A B).after [Ev.sample r] =
      some (Prog.read fun c₀ ↦ Prog.read fun c₁ ↦
        if A r c₀ c₁ then Prog.ret (B r c₀ c₁) else Prog.fail) := rfl

/-- The node after the challenge and the first value. -/
theorem sampleReadRead_after_two (r c₀ : E) :
    (sampleReadRead A B).after [Ev.sample r, Ev.read c₀] =
      some (Prog.read fun c₁ ↦ if A r c₀ c₁ then Prog.ret (B r c₀ c₁) else Prog.fail) := rfl

/-- The node after the challenge and both values. -/
theorem sampleReadRead_after_three (r c₀ c₁ : E) :
    (sampleReadRead A B).after [Ev.sample r, Ev.read c₀, Ev.read c₁] =
      some (if A r c₀ c₁ then Prog.ret (B r c₀ c₁) else Prog.fail) := by
  show Prog.after (if A r c₀ c₁ then Prog.ret (B r c₀ c₁) else Prog.fail) [] = _
  split <;> rfl

/-- The local runs of the program: the empty one, the challenge, then one and two values. -/
theorem sampleReadRead_reach {h₀ l : List Ev} (h : (sampleReadRead A B).Reach h₀ l) :
    l = [] ∨ (∃ r, l = [Ev.sample r]) ∨ (∃ r c₀, l = [Ev.sample r, Ev.read c₀]) ∨
      ∃ r c₀ c₁, l = [Ev.sample r, Ev.read c₀, Ev.read c₁] := by
  induction h with
  | nil => exact Or.inl rfl
  | read x _ ha ih =>
    rcases ih with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · cases ha
    · exact Or.inr (Or.inr (Or.inl ⟨r, x, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨r, c₀, x, rfl⟩))
    · rw [sampleReadRead_after_three] at ha
      split at ha <;> cases ha
  | sample c _ ha ih =>
    rcases ih with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · exact Or.inr (Or.inl ⟨c, rfl⟩)
    · cases ha
    · cases ha
    · rw [sampleReadRead_after_three] at ha
      split at ha <;> cases ha
  | grind _ ha ih =>
    rcases ih with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · cases ha
    · cases ha
    · cases ha
    · rw [sampleReadRead_after_three] at ha
      split at ha <;> cases ha
  | commit _ _ ha _ ih =>
    rcases ih with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · cases ha
    · cases ha
    · cases ha
    · rw [sampleReadRead_after_three] at ha
      split at ha <;> cases ha
  | query _ ha _ ih =>
    rcases ih with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · cases ha
    · cases ha
    · cases ha
    · rw [sampleReadRead_after_three] at ha
      split at ha <;> cases ha

/-- A return happens after both values, where `A` holds, and returns `B`. -/
theorem sampleReadRead_after_ret {h₀ l : List Ev} {a : β}
    (h : (sampleReadRead A B).Reach h₀ l) (ha : (sampleReadRead A B).after l = some (.ret a)) :
    ∃ r c₀ c₁, l = [Ev.sample r, Ev.read c₀, Ev.read c₁] ∧ A r c₀ c₁ ∧ a = B r c₀ c₁ := by
  rcases sampleReadRead_reach A B h with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
  · cases ha
  · cases ha
  · cases ha
  · rw [sampleReadRead_after_three] at ha
    split at ha
    · rename_i hA
      cases ha
      exact ⟨r, c₀, c₁, rfl, hA, rfl⟩
    · cases ha

end Shape

/-! ## The specification -/

section Spec

variable (A : E → E → E → Prop) [∀ r c₀ c₁, Decidable (A r c₀ c₁)] (B : E → E → E → β)
  (Good : List Ev → E → E → E → Prop)

/-- Doom of the shape: `Pre` at the start, then no good completion of the transcript so far. -/
def srrD (Pre : List Ev → Prop) (h₀ : List Ev) : List Ev → Prop
  | [] => Pre h₀
  | [Ev.sample r] => ¬ ∃ c₀ c₁, Good h₀ r c₀ c₁
  | [Ev.sample r, Ev.read c₀] => ¬ ∃ c₁, Good h₀ r c₀ c₁
  | [Ev.sample r, Ev.read c₀, Ev.read c₁] => ¬ Good h₀ r c₀ c₁
  | _ => True

/-- The escape potential of the shape: the probability over the challenge that some completion
is good; then the indicator of a good completion; at the end, the follower's allowance in doom. -/
noncomputable def srrV (T : ℝ≥0∞) (h₀ : List Ev) : List Ev → ℝ≥0∞
  | [] => avgE fun r ↦ indE (∃ c₀ c₁, Good h₀ r c₀ c₁)
  | [Ev.sample r] => indE (∃ c₀ c₁, Good h₀ r c₀ c₁)
  | [Ev.sample r, Ev.read c₀] => indE (∃ c₁, Good h₀ r c₀ c₁)
  | [Ev.sample r, Ev.read c₀, Ev.read c₁] => max (indE (Good h₀ r c₀ c₁)) (min 1 T)
  | _ => 1

/-- **The specification of the shape.** From

* `hesc`: under `Pre`, the probability over the challenge that some completion is good is at
  most `L`;
* `hpost`: a return in doom (`A` holds and the completion is not good) satisfies `Post`;
* `hT`: the follower's allowance is within `εmax`,

the program is specified with lead `L` and allowance `T`. -/
noncomputable def sampleReadReadSpec {Pre : List Ev → Prop} {Post : β → List Ev → Prop}
    {εmax L T : ℝ≥0∞}
    (hesc : ∀ h₀, Pre h₀ → avgE (fun r ↦ indE (∃ c₀ c₁, Good h₀ r c₀ c₁)) ≤ L)
    (hpost : ∀ h₀ r c₀ c₁, A r c₀ c₁ → ¬ Good h₀ r c₀ c₁ →
      Post (B r c₀ c₁) (h₀ ++ [Ev.sample r, Ev.read c₀, Ev.read c₁]))
    (hT : T ≤ εmax) :
    Spec (sampleReadRead A B) Pre Post εmax L T where
  D := srrD Good Pre
  V := srrV Good T
  le_one h₀ l := by
    unfold srrV
    split
    · exact avgE_indE_le_one _
    · exact indE_le_one _
    · exact indE_le_one _
    · exact max_le (indE_le_one _) (min_le_left _ _)
    · exact le_rfl
  start_D _ h := h
  start_V h₀ h := hesc h₀ h
  read := by
    intro h₀ l k x hr ha hD
    rcases sampleReadRead_reach A B hr with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · cases ha
    · exact fun ⟨c₁, hg⟩ ↦ hD ⟨x, c₁, hg⟩
    · exact fun hg ↦ hD ⟨x, hg⟩
    · rw [sampleReadRead_after_three] at ha
      split at ha <;> cases ha
  grind := by
    intro h₀ l b k hr ha _
    rcases sampleReadRead_reach A B hr with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · cases ha
    · cases ha
    · cases ha
    · rw [sampleReadRead_after_three] at ha
      split at ha <;> cases ha
  commit := by
    intro h₀ l ht w k word hr ha _ _
    rcases sampleReadRead_reach A B hr with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · cases ha
    · cases ha
    · cases ha
    · rw [sampleReadRead_after_three] at ha
      split at ha <;> cases ha
  sample := by
    intro h₀ l k hr ha
    rcases sampleReadRead_reach A B hr with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · exact le_rfl
    · cases ha
    · cases ha
    · rw [sampleReadRead_after_three] at ha
      split at ha <;> cases ha
  query := by
    intro h₀ l i ps k rows hr ha _
    rcases sampleReadRead_reach A B hr with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · cases ha
    · cases ha
    · cases ha
    · rw [sampleReadRead_after_three] at ha
      split at ha <;> cases ha
  moveEnd := by
    intro h₀ l q hr ha hq hD
    rcases sampleReadRead_reach A B hr with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · cases ha
      exact hq.elim
    · exact (indE_of (not_not.mp hD)).ge
    · exact (indE_of (not_not.mp hD)).ge
    · rw [sampleReadRead_after_three] at ha
      split at ha <;> cases ha <;> exact hq.elim
  retEnd := by
    intro h₀ l a hr ha hD
    obtain ⟨r, c₀, c₁, rfl, -, -⟩ := sampleReadRead_after_ret A B hr ha
    exact (indE_of (not_not.mp hD)).ge.trans (le_max_left _ _)
  retDoom := by
    intro h₀ l a hr ha _
    obtain ⟨r, c₀, c₁, rfl, -, -⟩ := sampleReadRead_after_ret A B hr ha
    exact le_max_right _ _
  post := by
    intro h₀ l a hr ha hD
    obtain ⟨r, c₀, c₁, rfl, hA, rfl⟩ := sampleReadRead_after_ret A B hr ha
    exact hpost h₀ r c₀ c₁ hA hD
  bound := by
    intro h₀ l hr hne hend hD
    rcases sampleReadRead_reach A B hr with rfl | ⟨r, rfl⟩ | ⟨r, c₀, rfl⟩ | ⟨r, c₀, c₁, rfl⟩
    · exact absurd rfl hne
    · exact hend.elim
    · show (2 : ℝ≥0∞)⁻¹ ^ 0 * indE (∃ c₁, Good h₀ r c₀ c₁) ≤ εmax
      rw [indE_of_not hD, mul_zero]
      exact zero_le
    · show (2 : ℝ≥0∞)⁻¹ ^ 0 * max (indE (Good h₀ r c₀ c₁)) (min 1 T) ≤ εmax
      rw [indE_of_not hD, pow_zero, one_mul, max_eq_right zero_le]
      exact (min_le_right _ _).trans hT

end Spec

end
end LeanerVM.Protocol.EndToEnd.Front
