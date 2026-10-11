/-
  LeanerVM.Protocol.ToClean.ComponentPolynomial

  A flat Clean component as one table of the M3 model: its constraint polynomials, its bus
  flushes and its count columns. A candidate for Clean.
-/

module

public import LeanerVM.Protocol.ToClean.ExpressionPolynomial
public import Clean.Air.FlatComponent

@[expose] public section

/-!
# Clean components as polynomial tables

The M3 model reads a table as polynomials in its row's variables: a constraint is a polynomial
that vanishes on every row, and a flush is a side of the bus with sixteen coordinate
polynomials, a domain separator first. Clean writes the same table as a component whose circuit
records, per row, `assert` expressions and channel interactions. This module is the
translation, generic over the field, the component and the type of bus sides.

* `Component.toM3 c sep dir counted` is the component `c` as one table of width `c.width`: its
  constraints are its `assert` expressions as polynomials; its flushes are its interactions,
  each on the side `dir` names for its channel, the separator `sep` names first, then the
  message's coordinates, then zeros (`flushPolys`); its count columns are the coordinate-`1`
  variables of the interactions on the channels `counted` selects, in column order and each
  once. The separators, the sides and the counted channels are explicit data, so the map from
  Clean's channels to the bus is stated, not inferred.
* `toM3_constraints_iff`: on a row of `c.width` cells, the constraint polynomials vanish
  exactly when Clean's constraints hold, for a component without lookups (Clean's
  `ConstraintsHold` is its `assert` expressions and its lookups).
* `toM3_flushes_eq`: on such a row, the flush polynomials evaluate to the sixteen-slot tuples
  `flushTuple sep` of the interactions Clean evaluates on the row, with their sides.
* `mem_toM3_count_iff` and `msg_one_of_countVar`: a count column is the variable of coordinate
  `1` of a counted interaction, and that coordinate evaluates to the column's cell. Under
  `CountsAreVariables`, which a component's data decides, every counted interaction has one
  (`exists_count_of_counted`).
* `tupleMsg_flushTuple`: a message of at most fifteen coordinates is read back off its tuple,
  so the tuples of one channel's messages determine the messages.

Written from the M3 model of leanVM's specification (§5.1 "The bus", §5.5 "The zerocheck") and
Clean's semantics of a flat component at `42fe4b26` (`Clean/Air/FlatComponent.lean`,
`Clean/Circuit/Operations.lean`).

## Wrong readings excluded

* A flush carries no multiplicity: the side is the channel's (`dir`), never the sign of a
  multiplicity, which carries none in characteristic two.
* A message longer than fifteen coordinates is truncated by the sixteen-slot tuple.
-/

namespace LeanerVM.Protocol

open CPoly Air.Flat

variable {F : Type} [FiniteField F] [DecidableEq F] {σ : Type}

/-! ## Flushes -/

/-- The sixteen coordinate polynomials of an interaction in a row of `n` variables: the
separator `sep` names for its channel, then the message's coordinates, then zeros. -/
def flushPolys (sep : RawChannel F → F) (n : ℕ) (i : AbstractInteraction F) :
    Vector (CMvPolynomial n F) 16 :=
  Vector.ofFn fun k ↦
    if k.val = 0 then CMvPolynomial.C (sep i.channel)
    else ((i.msg.toArray[k.val - 1]?).map (·.toCMvPolynomial n)).getD 0

/-- The sixteen-slot tuple of an evaluated interaction: the separator, then the message, then
zeros. -/
def flushTuple (sep : RawChannel F → F) (i : Interaction F) : Vector F 16 :=
  Vector.ofFn fun k ↦ if k.val = 0 then sep i.channel else i.msg[k.val - 1]?.getD 0

/-- The flush polynomials evaluate, at a row, to the tuple of the interaction evaluated on the
row. -/
theorem flushPolys_eval (sep : RawChannel F → F) {n : ℕ} (row : Fin n → F)
    (data : ProverData F) (i : AbstractInteraction F) :
    (flushPolys sep n i).map (·.eval row) =
      flushTuple sep (i.eval (Environment.fromArray (Array.ofFn row) data)) := by
  apply Vector.ext
  intro k hk
  simp only [flushPolys, flushTuple, Vector.getElem_map, Vector.getElem_ofFn]
  split_ifs
  · exact CMvPolynomial.eval_C _ _
  · have : (AbstractInteraction.eval (Environment.fromArray (Array.ofFn row) data) i).msg =
        (i.msg.toArray.map (Expression.eval (Environment.fromArray (Array.ofFn row) data))) := by
      simp [AbstractInteraction.eval]
    rw [this, Array.getElem?_map]
    cases i.msg.toArray[k - 1]? with
    | none => simp [CMvPolynomial.eval_zero]
    | some e => simp [Expression.eval_toCMvPolynomial row data]

/-- The first `a` message coordinates of a sixteen-slot tuple, after its separator. -/
def tupleMsg (a : ℕ) (v : Vector F 16) : Array F := Array.ofFn fun k : Fin a ↦ v[k.val + 1]?.getD 0

omit [DecidableEq F] in
/-- A message of at most fifteen coordinates is read back off its tuple: the tuple determines
the message, given its length. -/
theorem tupleMsg_flushTuple (sep : RawChannel F → F) (i : Interaction F) (h : i.msg.size ≤ 15) :
    tupleMsg i.msg.size (flushTuple sep i) = i.msg := by
  apply Array.ext (by simp [tupleMsg])
  intro k _ hk
  simp only [tupleMsg, Array.getElem_ofFn]
  rw [Vector.getElem?_eq_getElem (by omega), Option.getD_some]
  simp only [flushTuple, Vector.getElem_ofFn, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
  rw [Array.getElem?_eq_getElem hk, Option.getD_some]

/-- The flush polynomials' total degree is at most `d` when every message coordinate's
syntactic degree is: the separator is a constant, the padding zero. -/
theorem totalDegree_flushPolys_le (sep : RawChannel F → F) {n d : ℕ} (i : AbstractInteraction F)
    (h : ∀ e ∈ i.msg.toList, e.degreeBound ≤ d) (k : Fin 16) :
    ((flushPolys sep n i).get k).totalDegree ≤ d := by
  simp only [flushPolys, Vector.get_ofFn]
  split_ifs
  · rw [CPoly.totalDegree_equiv (S := F), CMvPolynomial.fromCMvPolynomial_C,
      MvPolynomial.totalDegree_C]
    exact Nat.zero_le _
  · cases he : i.msg.toArray[k.val - 1]? with
    | none =>
      rw [Option.map_none, Option.getD_none, CPoly.totalDegree_equiv (S := F), CPoly.map_zero,
        MvPolynomial.totalDegree_zero]
      exact Nat.zero_le _
    | some e =>
      rw [Option.map_some, Option.getD_some]
      refine (Expression.totalDegree_toCMvPolynomial_le _ e).trans (h e ?_)
      rw [← Vector.toList_toArray]
      exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? he)

/-! ## A component as an M3 table -/

/-- One table of the M3 model: its width, constraint polynomials, flushes (a side and
sixteen coordinate polynomials, separator first) and count columns. -/
structure M3Table (F : Type) [FiniteField F] (σ : Type) where
  /-- The number of columns. -/
  width : ℕ
  /-- The polynomials that vanish on every row. -/
  constraints : List (CMvPolynomial width F)
  /-- The bus flushes of a row. -/
  flushes : List (σ × Vector (CMvPolynomial width F) 16)
  /-- The columns whose cells must be nonzero. -/
  count : List (Fin width)

/-- The count column of an interaction: its coordinate `1`, when that is a variable below
`n`. -/
def countVar (n : ℕ) (i : AbstractInteraction F) : Option (Fin n) :=
  match i.msg.toArray[1]? with
  | some (Expression.var v) => if h : v.index < n then some ⟨v.index, h⟩ else none
  | _ => none

/-- The component `c` as one M3 table: its `assert` expressions as polynomials; its
interactions as flushes, on the side `dir` names for the channel, with the separator `sep`
names; and as count columns, the coordinate-`1` variables of the interactions on the channels
`counted` selects, in column order and each once. -/
def _root_.Air.Flat.Component.toM3 (c : Component F) (sep : RawChannel F → F)
    (dir : RawChannel F → σ) (counted : RawChannel F → Bool) : M3Table F σ where
  width := c.width
  constraints := c.rowOperations.constraints.map (·.toCMvPolynomial c.width)
  flushes := c.rowOperations.interactions.map fun i ↦ (dir i.channel, flushPolys sep c.width i)
  count := (List.finRange c.width).filter fun k ↦
    c.rowOperations.interactions.any fun i ↦ counted i.channel && countVar c.width i == some k

variable (c : Component F) (sep : RawChannel F → F) (dir : RawChannel F → σ)
  (counted : RawChannel F → Bool)

/-- On a row of `c.width` cells, the constraint polynomials vanish exactly when Clean's
constraints hold, for a component without lookups. -/
theorem toM3_constraints_iff (hl : c.rowOperations.lookups = []) (row : Fin c.width → F)
    (data : ProverData F) :
    (∀ C ∈ (c.toM3 sep dir counted).constraints, C.eval row = 0) ↔
      c.operations.ConstraintsHold (Environment.fromArray (Array.ofFn row) data) := by
  rw [Component.constraintsHold_iff, Operations.ConstraintsHold, hl]
  simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
  show (∀ C ∈ c.rowOperations.constraints.map (·.toCMvPolynomial c.width), _) ↔ _
  simp only [List.forall_mem_map, Expression.eval_toCMvPolynomial row data]

/-- On a row of `c.width` cells, the flushes evaluate to the tuples of the interactions Clean
evaluates on the row, each on its channel's side. -/
theorem toM3_flushes_eq (row : Fin c.width → F) (data : ProverData F) :
    (c.toM3 sep dir counted).flushes.map (fun f ↦ (f.1, f.2.map (·.eval row))) =
      (c.operations.interactionValues (Environment.fromArray (Array.ofFn row) data)).map
        fun i ↦ (dir i.channel, flushTuple sep i) := by
  rw [Component.interactionsValues_eq]
  simp only [Component.toM3, Operations.interactionValues, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, flushPolys_eval sep row data, AbstractInteraction.eval]

/-- A count column is the coordinate-`1` variable of a counted interaction. -/
theorem mem_toM3_count_iff (k : Fin c.width) :
    k ∈ (c.toM3 sep dir counted).count ↔
      ∃ i ∈ c.rowOperations.interactions, counted i.channel ∧ countVar c.width i = some k := by
  show k ∈ List.filter _ _ ↔ _
  simp [List.mem_filter, List.any_eq_true]

/-- The constraint polynomials' total degree is at most `d` when every `assert` expression's
syntactic degree is. -/
theorem toM3_constraints_degree {d : ℕ}
    (h : ∀ e ∈ c.rowOperations.constraints, e.degreeBound ≤ d) :
    ∀ C ∈ (c.toM3 sep dir counted).constraints, C.totalDegree ≤ d := by
  show ∀ C ∈ c.rowOperations.constraints.map (·.toCMvPolynomial c.width), _
  simp only [List.forall_mem_map]
  exact fun e he ↦ (Expression.totalDegree_toCMvPolynomial_le _ e).trans (h e he)

/-- The flush polynomials' total degree is at most `d` when every message coordinate's
syntactic degree is: the separator is a constant, the padding zero. -/
theorem toM3_flushes_degree {d : ℕ}
    (h : ∀ i ∈ c.rowOperations.interactions, ∀ e ∈ i.msg.toList, e.degreeBound ≤ d) :
    ∀ f ∈ (c.toM3 sep dir counted).flushes, ∀ k, (f.2.get k).totalDegree ≤ d := by
  intro f hf k
  have hf' : f ∈ c.rowOperations.interactions.map fun i ↦
      (dir i.channel, flushPolys sep c.width i) := hf
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf'
  exact totalDegree_flushPolys_le sep i (h i hi) k

/-- Every counted interaction's coordinate `1` is a variable below the width: no read count
is a constant or out of the row. -/
def CountsAreVariables : Prop :=
  ∀ i ∈ c.rowOperations.interactions, counted i.channel → (countVar c.width i).isSome

instance : Decidable (CountsAreVariables c counted) :=
  inferInstanceAs (Decidable (∀ i ∈ c.rowOperations.interactions, _))

/-- When counts are variables, every counted interaction has a count column. -/
theorem exists_count_of_counted (h : CountsAreVariables c counted)
    {i : AbstractInteraction F} (hi : i ∈ c.rowOperations.interactions) (hc : counted i.channel) :
    ∃ k ∈ (c.toM3 sep dir counted).count, countVar c.width i = some k := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp (h i hi hc)
  exact ⟨k, (mem_toM3_count_iff c sep dir counted k).mpr ⟨i, hi, hc, hk⟩, hk⟩

omit [DecidableEq F] in
/-- Coordinate `1` of an interaction whose count column is `k` evaluates, on a row, to the
row's cell `k`. -/
theorem msg_one_of_countVar {n : ℕ} {i : AbstractInteraction F} {k : Fin n}
    (h : countVar n i = some k) (row : Fin n → F) (data : ProverData F) :
    (i.eval (Environment.fromArray (Array.ofFn row) data)).msg[1]? = some (row k) := by
  unfold countVar at h
  simp only [AbstractInteraction.eval, Vector.toArray_map, Array.getElem?_map]
  split at h
  · next v hv =>
    split_ifs at h with hn
    obtain rfl := Option.some.inj h
    rw [hv]
    simp [Expression.eval, Environment.fromArray, Array.getElem?_ofFn, hn]
  · exact absurd h (by simp)

end LeanerVM.Protocol
