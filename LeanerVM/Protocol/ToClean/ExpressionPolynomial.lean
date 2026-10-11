/-
  LeanerVM.Protocol.ToClean.ExpressionPolynomial

  A Clean expression as a computable polynomial in a row's variables, with its syntactic degree
  and its width. A candidate for Clean.
-/

module

public import Clean.Circuit.Expression
public import CompPoly.Multivariate.Eval
public import CompPoly.Multivariate.MvPolyEquiv.Eval

@[expose] public section

/-!
# Clean expressions as polynomials

A Clean expression is a sum and product of a row's variables and constants. Read as a
polynomial in the row's `n` variables, it vanishes on a row exactly when Clean's evaluation of
it does; its degree is bounded by its syntax.

* `Expression.toCMvPolynomial n e` is `e` as a CompPoly polynomial in `n` variables: variable
  `i` is `X i` when `i < n` and `0` otherwise, constants are constants, sum and product are sum
  and product. It is computable. `eval_toCMvPolynomial`: it evaluates, at a row of `n` cells,
  to Clean's evaluation of `e` on that row. Clean reads a missing cell as `0`, which is what the
  translation makes of a variable at or beyond `n`.
* `Expression.degreeBound` is the syntactic degree (a variable `1`, a constant `0`, a sum the
  larger, a product the sum); `totalDegree_toCMvPolynomial_le` bounds the polynomial's total
  degree by it.
* `Expression.WithinWidth n e`, every variable of `e` is below `n`, is decidable; under it
  Clean's evaluation reads only the first `n` cells of a row (`eval_fromArray_truncate`).

Clean's own `Clean/Circuit/ExpressionPolynomial.lean` (Clean pull request 466, on Clean's main
but not in a revision built for this repository's Lean) defines `degreeBound` and
`WithinWidth` with the same clauses, and the noncomputable Mathlib polynomial
`toBoundedPolynomial`. Once the pin contains it, the two definitions here are deleted in favour
of Clean's, and the computable translation stays, proved equal to `toBoundedPolynomial` within
the width.

Written from Clean's semantics of an expression at `42fe4b26` (`Clean/Circuit/Expression.lean`).

## Wrong readings excluded

* A variable at or beyond the width is not a free variable of the polynomial: it is `0`, as
  Clean's `Environment.fromArray` reads a missing cell.
* The degree bound is syntactic and can exceed the polynomial's degree (`x · y + x · y` is
  `2 · x · y`, `x · y - x · y` is `0`); it is an upper bound, never the degree.
-/

namespace Expression

open CPoly

variable {F : Type} [Field F] [DecidableEq F]

/-- The expression as a polynomial in `n` variables: variable `i` is `X i` when `i < n` and `0`
otherwise, as Clean reads a missing cell. -/
def toCMvPolynomial (n : ℕ) : Expression F → CMvPolynomial n F
  | var v => if h : v.index < n then CMvPolynomial.X ⟨v.index, h⟩ else 0
  | const c => CMvPolynomial.C c
  | add x y => x.toCMvPolynomial n + y.toCMvPolynomial n
  | mul x y => x.toCMvPolynomial n * y.toCMvPolynomial n

/-- The polynomial evaluates, at a row of `n` cells, to Clean's evaluation of the expression on
that row, over any prover data. -/
theorem eval_toCMvPolynomial {n : ℕ} (row : Fin n → F) (data : ProverData F)
    (e : Expression F) :
    (e.toCMvPolynomial n).eval row = e.eval (Environment.fromArray (Array.ofFn row) data) := by
  induction e with
  | var v =>
    simp only [toCMvPolynomial, eval]
    split_ifs with h
    · simp [CMvPolynomial.eval_X, h]
    · simp [CMvPolynomial.eval_zero, h]
  | const c => simp only [toCMvPolynomial, eval, CMvPolynomial.eval_C]
  | add x y hx hy => simp only [toCMvPolynomial, eval, CMvPolynomial.eval_add, hx, hy]
  | mul x y hx hy => simp only [toCMvPolynomial, eval, CMvPolynomial.eval_mul, hx, hy]

/-- The syntactic degree: a variable `1`, a constant `0`, a sum the larger of its terms', a
product the sum of its factors'. -/
def degreeBound : Expression F → ℕ
  | var _ => 1
  | const _ => 0
  | add x y => max x.degreeBound y.degreeBound
  | mul x y => x.degreeBound + y.degreeBound

/-- The syntactic degree bounds the polynomial's total degree. -/
theorem totalDegree_toCMvPolynomial_le (n : ℕ) (e : Expression F) :
    (e.toCMvPolynomial n).totalDegree ≤ e.degreeBound := by
  rw [CPoly.totalDegree_equiv (S := F)]
  induction e with
  | var v =>
    simp only [toCMvPolynomial, degreeBound]
    split_ifs
    · rw [CMvPolynomial.fromCMvPolynomial_X]
      rw [MvPolynomial.totalDegree_X]
    · rw [CPoly.map_zero, MvPolynomial.totalDegree_zero]
      exact Nat.zero_le _
  | const c =>
    rw [toCMvPolynomial, CMvPolynomial.fromCMvPolynomial_C, MvPolynomial.totalDegree_C]
    exact Nat.zero_le _
  | add x y hx hy =>
    rw [toCMvPolynomial, CPoly.map_add]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max hx hy)
  | mul x y hx hy =>
    rw [toCMvPolynomial, CPoly.map_mul]
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hx hy)

/-- Every variable of the expression is below `n`. -/
def WithinWidth (n : ℕ) : Expression F → Prop
  | var v => v.index < n
  | const _ => True
  | add x y => x.WithinWidth n ∧ y.WithinWidth n
  | mul x y => x.WithinWidth n ∧ y.WithinWidth n

instance instDecidableWithinWidth (n : ℕ) : (e : Expression F) → Decidable (e.WithinWidth n)
  | var v => inferInstanceAs (Decidable (v.index < n))
  | const _ => inferInstanceAs (Decidable True)
  | add x y =>
    have := instDecidableWithinWidth n x
    have := instDecidableWithinWidth n y
    inferInstanceAs (Decidable (_ ∧ _))
  | mul x y =>
    have := instDecidableWithinWidth n x
    have := instDecidableWithinWidth n y
    inferInstanceAs (Decidable (_ ∧ _))

omit [DecidableEq F] in
/-- An expression within width `n` reads only the first `n` cells of a row: its evaluation on
the row is its evaluation on those cells, a missing one `0`. -/
theorem eval_fromArray_truncate {n : ℕ} (row : Array F) (data : ProverData F)
    {e : Expression F} (h : e.WithinWidth n) :
    e.eval (Environment.fromArray row data) =
      e.eval (Environment.fromArray (Array.ofFn fun i : Fin n ↦ row[(i : ℕ)]?.getD 0) data) := by
  induction e with
  | var v =>
    simp [eval, show v.index < n from h]
  | const c => rfl
  | add x y hx hy => simp only [eval, hx h.1, hy h.2]
  | mul x y hx hy => simp only [eval, hx h.1, hy h.2]

end Expression
