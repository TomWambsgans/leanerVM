/-
  LeanerVM.Protocol.Verifier.TableSumcheck

  The batched table sumcheck of leanVM's Python verifier as a program of the verifier language:
  one back-loaded sumcheck over all six tables at the bus point, closed by the tables' row
  evaluations.
-/

module

public import LeanerVM.Protocol.Verifier.Layout
public import LeanerVM.Protocol.Verifier.Sumcheck

/-!
# The table sumcheck

Category B: transcribed from `python-verifier/verifier.py` at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, lines 598-626 (`table_sumcheck`).

One plain-mode sumcheck of four coefficients per round runs over `max` of the tables'
log-heights. Its challenges, reversed, are the point; a table of log-height `h` weighs the first
`h` coordinates by the equality with the bus point and every later one by the challenge itself
(`tableWeights`). The prover then sends each table's row evaluations, in table order, and the
terminal claim must be `Σ weight · (constraints + forms)`, the constraints batched by a disjoint
range of `constraint_powers` per table and the three sides' forms by `form_powers`. Each
evaluation becomes a claim on its global column at the point's first `h` coordinates.
-/

namespace LeanerVM.Protocol.Verifier

open LeanerVM.Parameters LeanerVM.Protocol.Compile

@[expose] public section

/-- The tables' weights at the point (`verifier.py:610-614`): coordinate `v` contributes
`1 + equality_point[v] + r_v` to a table taller than `v`, and `r_v` to the others. -/
def tableWeights (heights : List ℕ) (equalityPoint point : List E) : List E :=
  point.zipIdx.foldl (fun weights (challenge, coord) ↦
    let equality := 1 + equalityPoint.getD coord 0 + challenge
    List.zipWith (fun weight height ↦ weight * if coord < height then equality else challenge)
      weights heights) (heights.map fun _ ↦ 1)

/-- The per-table loop of `table_sumcheck` (`verifier.py:616-624`): read each table's row
evaluations, add its weighted terms to `final`, and collect its column claims. -/
def tableTerms (constraintPowers formPowers point : List E) :
    List (Table × ℕ × List Form × E) → ℕ → E → List ColumnClaim → Prog (E × List ColumnClaim)
  | [], _, final, claims => return (final, claims)
  | (table, height, forms, weight) :: rest, cursor, final, claims => do
    let evaluations ← Prog.readN table.width
    let summand := dot ((constraintPowers.drop cursor).take table.nConstraints)
      (table.constraints evaluations)
    let final := final +
      weight * (summand + dot formPowers (forms.map (·.evaluate (evaluations.getD · 0))))
    let claims := claims ++ evaluations.zipIdx.map fun (value, column) ↦
      ⟨globalColumnBases.getD table.opcode 0 + column, point.take height, value⟩
    tableTerms constraintPowers formPowers point rest (cursor + table.nConstraints) final claims

/-- `table_sumcheck(table_log_heights, bus_forms, constraint_powers, form_powers,
equality_point, target)` (`verifier.py:598-626`). -/
def tableSumcheck (heights : List ℕ) (busForms : List (List Form))
    (constraintPowers formPowers equalityPoint : List E) (target : E) :
    Prog (List ColumnClaim) := do
  let nRounds := heights.foldl max 0
  let (challenges, claim) ← sumcheck target 4 (List.replicate nRounds none)
  let point := challenges.reverse
  let weights := tableWeights heights equalityPoint point
  let rows := List.zip tables (List.zip heights (List.zip busForms weights))
  let (final, claims) ← tableTerms constraintPowers formPowers point rows 0 0 []
  Prog.require (final = claim)
  return claims

end
end LeanerVM.Protocol.Verifier
