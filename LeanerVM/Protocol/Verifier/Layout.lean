/-
  LeanerVM.Protocol.Verifier.Layout

  The data the Python verifier derives from the bytecode and the announced sizes: placements on
  the stacked cube, the bus layout, the degree-two forms the tables flush, the six instruction
  tables with their flushes and constraints, and `build_layout`.
-/

module

public import LeanerVM.Parameters.Whir
public import LeanerVM.Protocol.Verifier.Arith

/-!
# The verifier's layout

Category B: transcribed from `python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, lines 285-315 (`Placement`, `stack_offsets`,
`_selector_point`), 458-531 (`Form`, `BusBlock`, `BusLayout`, `bus_layout`, `ColumnClaim`), and
631-897 (the constants, `Layout`, `Flushes`, `Table`, the six tables, `build_layout`).

## Representation

* A `Form` is the Python's `dict` from monomials to coefficients, as an association list in
  insertion order: `addScaled` adds into an existing monomial's coefficient and appends a new
  one, as the `dict` does. A monomial is the sorted list of its column indices (`()`, `(i,)`,
  `(i, j)`).
* The Python's column-name lookups `_cols` are `colIdx`, `List.idxOf` on the column-name list;
  every name the tables use is in its list (`tests/LeanerVMTests/Protocol/Verifier/Layout.lean`
  checks the Python's `assert`).
* `Table.constraints` is a function of the row's evaluations, as in the Python; only `jump` has
  any (`_jump_constraints`).
* `build_layout` returns `none` exactly where the Python raises: a bytecode whose length is not
  a power of two (`log2_strict`), a bytecode shorter than `2^BUS_BITS` (negative
  `log_bytecode`), the size window, and a list of heights not one per table (the strict `zip`).
-/

namespace LeanerVM.Protocol.Verifier

open LeanerVM.Parameters

@[expose] public section

/-! ## Constants (`verifier.py:523, 631-645, 681-683, 823-855`) -/

/-- The bus communicates tuples of `2^BUS_BITS` field elements. -/
def busBits : ℕ := 4

/-- The columns no instruction table owns, first in the global numbering. -/
def numGlobalColumns : ℕ := 6

/-- Global column `MEMORY_0`. -/
def memory0 : ℕ := 0
/-- Global column `MEMORY_1`. -/
def memory1 : ℕ := 1
/-- Global column `MEMORY_2`. -/
def memory2 : ℕ := 2
/-- Global column `MEMORY_FINAL_COUNTERS`. -/
def memoryFinalCounters : ℕ := 3
/-- Global column `BYTECODE_FINAL_COUNTERS`. -/
def bytecodeFinalCounters : ℕ := 4
/-- Global column `QFLOCK`, the Flock witness region. -/
def qflock : ℕ := 5

/-- `BLAKE2S_R1CS_LOG_SIZE`: a Flock block has `2^14` positions. -/
def blake2sR1csLogSize : ℕ := 14

/-- `K_BITS`. -/
def kBits : ℕ := 64

/-- `FLOCK_K_SKIP = log2_ceil(K_BITS)`. -/
def flockKSkip : ℕ := log2Ceil kBits

/-- `LOG_PACKING = log2_ceil(K_BITS)`: bits per committed `K` element. -/
def logPacking : ℕ := log2Ceil kBits

/-- `FLOCK_NUM_LINCHECK_ROUNDS`. -/
def flockNumLincheckRounds : ℕ := blake2sR1csLogSize - flockKSkip

/-- `QFLOCK_SLOT_BITS`. -/
def qflockSlotBits : ℕ := blake2sR1csLogSize - logPacking

/-- `BLAKE2S_CONSTANT_COLUMN`: the constant wire of a Flock block. -/
def blake2sConstantColumn : ℕ := 512

/-- `MIN_STACKED_LOG`. -/
def minStackedLog : ℕ := Whir.minLogStack

/-- `MAX_STACKED_LOG`. -/
def maxStackedLog : ℕ := Whir.maxLogStack

/-- `SEP_STATE = ONE`. -/
def sepState : E := 1
/-- `SEP_MEM = GEN`. -/
def sepMem : E := gen
/-- `SEP_BYTECODE = GEN²`. -/
def sepBytecode : E := gen ^ 2

/-- Opcode `XOR`. -/
def opXor : ℕ := 0
/-- Opcode `MUL`. -/
def opMul : ℕ := 1
/-- Opcode `SET`. -/
def opSet : ℕ := 2
/-- Opcode `DEREF`. -/
def opDeref : ℕ := 3
/-- Opcode `JUMP`. -/
def opJump : ℕ := 4
/-- Opcode `BLAKE2S`. -/
def opBlake2s : ℕ := 5

/-! ## Placements (`verifier.py:285-315`) -/

/-- Where something sits in the stacked cube: a claim's point fills the `vars` coordinates
above `low`, the bits of `index` fixing the rest. -/
structure Placement where
  /-- The number of coordinates the claim's point fills. -/
  vars : ℕ
  /-- The selector whose bits fix the other coordinates. -/
  index : ℕ
  /-- The coordinates below the window. -/
  low : ℕ := 0
  deriving Inhabited, DecidableEq, Repr

/-- `Placement.stack_point`: the point on the stacked cube. -/
def Placement.stackPoint (p : Placement) (point : List E) (stackLog : ℕ) : List E :=
  let bits := selectorPoint p.index stackLog
  bits.take p.low ++ point ++ bits.drop (p.low + p.vars)

/-- `Placement.eq_above`: the equality weight of the coordinates above the window. -/
def Placement.eqAbove (p : Placement) (point : List E) : E :=
  let bits := selectorPoint (p.index >>> (p.low + p.vars))
    (point.length - p.low - p.vars)
  eqEval bits (point.drop (p.low + p.vars))

/-- `stack_offsets(sizes)`: blocks of `2^size` laid end to end, largest first, ties by index;
their offsets, and the log-size of the total (`verifier.py:304-310`). -/
def stackOffsets (sizes : List ℕ) : List ℕ × ℕ :=
  let size := fun i ↦ sizes.getD i 0
  let order := (List.range sizes.length).mergeSort fun i j ↦
    decide (size j < size i) || (decide (size i = size j) && decide (i ≤ j))
  let placed := order.foldl (fun (acc : List ℕ × ℕ) i ↦
    (acc.1.set i acc.2, acc.2 + 2 ^ size i)) (List.replicate sizes.length 0, 0)
  (placed.1, log2Ceil placed.2)

/-! ## Forms (`verifier.py:458-480`) -/

/-- A polynomial of degree at most two in a table's columns: monomial (sorted column indices) to
coefficient, in insertion order. -/
structure Form where
  /-- The terms. -/
  terms : List (List ℕ × E) := []
  deriving Inhabited

/-- Add `c` into the coefficient of `m`, appending the monomial if it is new (the `dict`
update). -/
def addTerm : List (List ℕ × E) → List ℕ → E → List (List ℕ × E)
  | [], m, c => [(m, 0 + c)]
  | (m', c') :: rest, m, c =>
    if m' = m then (m', c' + c) :: rest else (m', c') :: addTerm rest m c

/-- `Form.add_scaled`: add `weight · other`. -/
def Form.addScaled (f other : Form) (weight : E) : Form :=
  ⟨other.terms.foldl (fun acc t ↦ addTerm acc t.1 (weight * t.2)) f.terms⟩

/-- `Form.__add__`. -/
def Form.add (f g : Form) : Form := f.addScaled g 1

/-- `Form.sum`: the empty sum is the zero polynomial. -/
def Form.sum (forms : List Form) : Form := forms.foldl Form.add {}

/-- `Form.evaluate`: `Σ c · Π column(i)` over the terms. -/
def Form.evaluate (f : Form) (column : ℕ → E) : E :=
  sumE (f.terms.map fun t ↦ t.1.foldl (fun acc i ↦ acc * column i) t.2)

/-- `_const(value)`. -/
def Form.const (value : E) : Form := ⟨[([], value)]⟩

/-- `_col(index, exponent)`: `g^exponent · x_index`. -/
def Form.col (index : ℕ) (exponent : ℕ := 0) : Form := ⟨[([index], gpow exponent)]⟩

/-- `_prod(a, b, exponent)`: `g^exponent · x_a · x_b`. -/
def Form.prod (a b : ℕ) (exponent : ℕ := 0) : Form := ⟨[([min a b, max a b], gpow exponent)]⟩

/-! ## Flushes (`verifier.py:686-711`) -/

/-- A table's bus flushes: the tuples it pushes and pulls, in pairs. -/
structure Flushes where
  /-- The pushed tuples. -/
  push : List (List Form) := []
  /-- The pulled tuples. -/
  pull : List (List Form) := []
  deriving Inhabited

namespace Flushes

/-- `Flushes.pair`. -/
def pair (f : Flushes) (push pull : List Form) : Flushes := ⟨f.push ++ [push], f.pull ++ [pull]⟩

/-- `Flushes.state_derived`. -/
def stateDerived (f : Flushes) (pc fp : ℕ) (npc nfp : Form) : Flushes :=
  f.pair [Form.const sepState, npc, nfp] [Form.const sepState, Form.col pc, Form.col fp]

/-- `Flushes.state_step`. -/
def stateStep (f : Flushes) (pc fp : ℕ) : Flushes :=
  f.stateDerived pc fp (Form.col pc 1) (Form.col fp)

/-- `Flushes._counted`. -/
def counted (f : Flushes) (pre : List Form) (count : ℕ) (suffix : List Form) : Flushes :=
  f.pair (pre ++ [Form.col count 1] ++ suffix) (pre ++ [Form.col count] ++ suffix)

/-- `Flushes.bytecode`. -/
def bytecode (f : Flushes) (pc count opcode : ℕ) (operands : List Form) : Flushes :=
  f.counted [Form.const sepBytecode, Form.col pc] count (Form.const (gpow opcode) :: operands)

/-- `Flushes.memory`. -/
def memory (f : Flushes) (address : Form) (count : ℕ) (values : List Form) : Flushes :=
  f.counted [Form.const sepMem, address] count values

/-- `Flushes.memory_cols`: the columns, padded with zeros to three limbs. -/
def memoryCols (f : Flushes) (address : Form) (count : ℕ) (columns : List ℕ) : Flushes :=
  f.memory address count
    (columns.map (Form.col ·) ++ List.replicate (3 - columns.length) (Form.const 0))

end Flushes

/-! ## The instruction tables (`verifier.py:717-855`) -/

/-- `_cols(columns, name)`: the index of a column by name. -/
def colIdx (columns : List String) (name : String) : ℕ := columns.idxOf name

/-- `ARITH_COLUMNS`. -/
def arithColumns : List String :=
  ["pc", "fp", "o_a", "o_b", "o_c", "va_0", "va_1", "va_2", "vb_0", "vb_1", "vb_2", "cnt_a",
    "cnt_b", "cnt_c", "cnt_bc"]

/-- `SET_COLUMNS`. -/
def setColumns : List String := ["pc", "fp", "o", "k_0", "k_1", "k_2", "cnt", "cnt_bc"]

/-- `DEREF_COLUMNS`. -/
def derefColumns : List String :=
  ["pc", "fp", "o1", "o2", "o3", "f_pc", "f_fp", "ptr", "v3_0", "v3_1", "v3_2", "cnt_ptr",
    "cnt_target", "cnt_local", "cnt_bc"]

/-- `JUMP_COLUMNS`. -/
def jumpColumns : List String :=
  ["pc", "fp", "o_c", "o_d", "o_f", "v_cond", "v_pc", "v_fp", "cnt_c", "cnt_d", "cnt_f", "cnt_bc",
    "w", "b"]

/-- `BLAKE2S_COLUMNS`. -/
def blake2sColumns : List String :=
  ["pc", "fp", "o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md",
    "m0_lo", "m0_hi", "m1_lo", "m1_hi", "m2_lo", "m2_hi", "m3_lo", "m3_hi",
    "out0_lo", "out0_hi", "out1_lo", "out1_hi", "cv0_lo", "cv0_hi", "cv1_lo", "cv1_hi", "md_lo",
    "md_hi",
    "cnt_m0", "cnt_m1", "cnt_m2", "cnt_m3", "cnt_cv0", "cnt_cv1", "cnt_out0", "cnt_out1", "cnt_md",
    "cnt_bc"]

/-- `TOWER_LANES`: the limb products of `E` multiplication folded by `y³ = y + 1`. -/
def towerLanes : List (List (ℕ × ℕ)) :=
  [[(0, 0), (1, 2), (2, 1)], [(0, 1), (1, 0), (1, 2), (2, 1), (2, 2)],
    [(0, 2), (1, 1), (2, 0), (2, 2)]]

/-- `_flushes_arith(opcode, multiply)` (`verifier.py:740-755`). -/
def flushesArith (opcode : ℕ) (multiply : Bool) : Flushes :=
  let c := colIdx arithColumns
  let va := [c "va_0", c "va_1", c "va_2"]
  let vb := [c "vb_0", c "vb_1", c "vb_2"]
  let result : List Form :=
    if multiply then
      towerLanes.map fun lane ↦
        Form.sum (lane.map fun (j, k) ↦ Form.prod (va.getD j 0) (vb.getD k 0))
    else (List.range 3).map fun i ↦ (Form.col (va.getD i 0)).add (Form.col (vb.getD i 0))
  let f : Flushes := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opcode
    [Form.col (c "o_a"), Form.col (c "o_b"), Form.col (c "o_c"), Form.const 0, Form.const 0]
  let f := f.memoryCols (Form.prod (c "fp") (c "o_a")) (c "cnt_a") va
  let f := f.memoryCols (Form.prod (c "fp") (c "o_b")) (c "cnt_b") vb
  f.memory (Form.prod (c "fp") (c "o_c")) (c "cnt_c") result

/-- `_flushes_set()` (`verifier.py:758-765`). -/
def flushesSet : Flushes :=
  let c := colIdx setColumns
  let k := [c "k_0", c "k_1", c "k_2"]
  let f : Flushes := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opSet
    (Form.col (c "o") :: k.map (Form.col ·) ++ [Form.const 0])
  f.memoryCols (Form.prod (c "fp") (c "o")) (c "cnt") k

/-- `_flushes_deref()` (`verifier.py:768-784`). -/
def flushesDeref : Flushes :=
  let c := colIdx derefColumns
  let pc := c "pc"
  let fp := c "fp"
  let fPc := c "f_pc"
  let fFp := c "f_fp"
  let v3 := [c "v3_0", c "v3_1", c "v3_2"]
  let gated := fun lane ↦ [Form.col lane, Form.prod fPc lane, Form.prod fFp lane]
  let store : List Form :=
    [Form.sum (gated (v3.getD 0 0) ++ [Form.prod fPc pc 2, Form.prod fFp fp]),
      Form.sum (gated (v3.getD 1 0)), Form.sum (gated (v3.getD 2 0))]
  let f : Flushes := {}
  let f := f.stateStep pc fp
  let f := f.bytecode pc (c "cnt_bc") opDeref
    [Form.col (c "o1"), Form.col (c "o2"), Form.col (c "o3"), Form.col fPc, Form.col fFp]
  let f := f.memoryCols (Form.prod fp (c "o1")) (c "cnt_ptr") [c "ptr"]
  let f := f.memory (Form.prod (c "ptr") (c "o2")) (c "cnt_target") store
  f.memoryCols (Form.prod fp (c "o3")) (c "cnt_local") v3

/-- `_flushes_jump()` (`verifier.py:787-797`): `next_pc = b·dest + (b + 1)·g·pc`,
`next_fp = b·frame + (b + 1)·fp`. -/
def flushesJump : Flushes :=
  let c := colIdx jumpColumns
  let pc := c "pc"
  let fp := c "fp"
  let b := c "b"
  let f : Flushes := {}
  let f := f.stateDerived pc fp
    (((Form.prod b (c "v_pc")).add (Form.prod b pc 1)).add (Form.col pc 1))
    (((Form.prod b (c "v_fp")).add (Form.prod b fp)).add (Form.col fp))
  let f := f.bytecode pc (c "cnt_bc") opJump
    [Form.col (c "o_c"), Form.col (c "o_d"), Form.col (c "o_f"), Form.const 0, Form.const 0]
  let f := f.memoryCols (Form.prod fp (c "o_c")) (c "cnt_c") [c "v_cond"]
  let f := f.memoryCols (Form.prod fp (c "o_d")) (c "cnt_d") [c "v_pc"]
  f.memoryCols (Form.prod fp (c "o_f")) (c "cnt_f") [c "v_fp"]

/-- `_jump_constraints(columns)`: `b + cond·w` and `cond·(b + 1)` (`verifier.py:800-802`). -/
def jumpConstraints (columns : List E) : List E :=
  let c := colIdx jumpColumns
  let condition := columns.getD (c "v_cond") 0
  let inverse := columns.getD (c "w") 0
  let flag := columns.getD (c "b") 0
  [flag + condition * inverse, condition * (flag + 1)]

/-- The nine `BLAKE2S` cells read, as (cell, operand, offset): `verifier.py:814-816`. -/
def blake2sCells : List (String × String × ℕ) :=
  [("m0", "o_0", 0), ("m1", "o_1", 0), ("m2", "o_2", 0), ("m3", "o_3", 0),
    ("cv0", "o_v", 0), ("cv1", "o_v", 1), ("out0", "o_out", 0), ("out1", "o_out", 1),
    ("md", "o_md", 0)]

/-- `_flushes_blake2s()` (`verifier.py:805-820`). -/
def flushesBlake2s : Flushes :=
  let c := colIdx blake2sColumns
  let operands := ["o_0", "o_1", "o_2", "o_3", "o_v", "o_out", "o_md"].map c
  let f : Flushes := {}
  let f := f.stateStep (c "pc") (c "fp")
  let f := f.bytecode (c "pc") (c "cnt_bc") opBlake2s (operands.map (Form.col ·))
  blake2sCells.foldl (fun f (cell, operand, exponent) ↦
    f.memoryCols (Form.prod (c "fp") (c operand) exponent) (c ("cnt_" ++ cell))
      [c (cell ++ "_lo"), c (cell ++ "_hi")]) f

/-- One instruction's table: its columns, its bus flushes, its constraints
(`verifier.py:717-737`). -/
structure Table where
  /-- The table's name. -/
  name : String
  /-- Its opcode, also its index in `TABLES`. -/
  opcode : ℕ
  /-- Its column names. -/
  columns : List String
  /-- Its flushes. -/
  flushes : Flushes
  /-- Its constraints, as a function of a row's evaluations. -/
  constraints : List E → List E := fun _ ↦ []
  deriving Inhabited

/-- `Table.width`. -/
def Table.width (t : Table) : ℕ := t.columns.length

/-- `Table.n_constraints`: the number of constraints, read off the zero row. -/
def Table.nConstraints (t : Table) : ℕ := (t.constraints (List.replicate t.width 0)).length

/-- `Table.count_columns`: the columns whose name starts with `cnt`. -/
def Table.countColumns (t : Table) : List ℕ :=
  (t.columns.zipIdx.filter fun (name, _) ↦ name.startsWith "cnt").map (·.2)

/-- `TABLES`, in opcode order (`verifier.py:838-845`). -/
def tables : List Table :=
  [⟨"xor", opXor, arithColumns, flushesArith opXor false, fun _ ↦ []⟩,
    ⟨"mul", opMul, arithColumns, flushesArith opMul true, fun _ ↦ []⟩,
    ⟨"set", opSet, setColumns, flushesSet, fun _ ↦ []⟩,
    ⟨"deref", opDeref, derefColumns, flushesDeref, fun _ ↦ []⟩,
    ⟨"jump", opJump, jumpColumns, flushesJump, jumpConstraints⟩,
    ⟨"blake2s", opBlake2s, blake2sColumns, flushesBlake2s, fun _ ↦ []⟩]

/-- `BLAKE2S_SLOTS`: the `BLAKE2S` limb each Flock slot carries; slots 8 and 9 carry none
(`verifier.py:849-852`). -/
def blake2sSlots : List (Option String) :=
  [some "cv0_lo", some "cv0_hi", some "cv1_lo", some "cv1_hi", some "out0_lo", some "out0_hi",
    some "out1_lo", some "out1_hi", none, none,
    some "m0_lo", some "m0_hi", some "m1_lo", some "m1_hi", some "m2_lo", some "m2_hi",
    some "m3_lo", some "m3_hi", some "md_lo", some "md_hi"]

/-- `TABLE_WIDTHS`. -/
def tableWidths : List ℕ := tables.map Table.width

/-- `GLOBAL_COLUMN_BASES`: each table's first global column. -/
def globalColumnBases : List ℕ :=
  (List.range tables.length).map fun t ↦ numGlobalColumns + (tableWidths.take t).sum

/-! ## The bus layout (`verifier.py:482-531`) -/

/-- One block of a bus side, owned by a table. -/
structure BusBlock where
  /-- The owner's log-height. -/
  logRows : ℕ
  /-- The tuple flushed, over the owner's local columns. -/
  coordinates : List Form
  /-- The owner's opcode. -/
  owner : ℕ
  deriving Inhabited

/-- Where a side's blocks sit in the stacked leaf cube. -/
structure BusLayout where
  /-- The log-size of the padded cube. -/
  depth : ℕ
  /-- The framework blocks' placements. -/
  framework : List Placement
  /-- The table blocks' placements, in the side's block order. -/
  tables : List Placement

/-- `bus_layout(framework_log_rows, blocks)` (`verifier.py:504-509`). -/
def busLayout (frameworkLogRows : List ℕ) (blocks : List BusBlock) : BusLayout :=
  let sizes := frameworkLogRows ++ blocks.map (·.logRows)
  let (offsets, depth) := stackOffsets sizes
  let placements := List.zipWith (fun size offset ↦ ({ vars := size, index := offset } :
    Placement)) sizes offsets
  ⟨depth, placements.take frameworkLogRows.length, placements.drop frameworkLogRows.length⟩

/-- A column claim: the column's multilinear extension at `point` is `value`. -/
structure ColumnClaim where
  /-- The global column. -/
  column : ℕ
  /-- The point, over the column's own variables. -/
  point : List E
  /-- The claimed value. -/
  value : E

/-- A claim on the stack: the weight it puts on the stack, and the value it claims for it. -/
abbrev StackClaim : Type := (List E → E) × E

/-! ## `build_layout` (`verifier.py:647-657, 858-897`) -/

/-- The layout the verifier derives from the bytecode and the announced sizes. -/
structure Layout where
  /-- The memory's log-size. -/
  logMemory : ℕ
  /-- The bytecode's log-size, in tuples of `2^BUS_BITS` words. -/
  logBytecode : ℕ
  /-- The bytecode's words. -/
  bytecode : List K
  /-- The push side's blocks. -/
  push : List BusBlock
  /-- The pull side's blocks. -/
  pull : List BusBlock
  /-- The count side's blocks. -/
  count : List BusBlock
  /-- Every global column's placement. -/
  placements : List Placement
  /-- The stacked cube's log-size. -/
  stackLog : ℕ
  /-- The tables' log-heights. -/
  tableLogHeights : List ℕ

/-- `ColumnClaim.on_stack`: the claim as an equality weight on the stack. -/
def ColumnClaim.onStack (c : ColumnClaim) (layout : Layout) : StackClaim :=
  let point := (layout.placements.getD c.column default).stackPoint c.point layout.stackLog
  (fun x ↦ eqEval point x, c.value)

/-- The bus blocks of every table, side by side: pushes, pulls, counts
(`verifier.py:868-878`). -/
def busBlocks (tableLogHeights : List ℕ) : List BusBlock × List BusBlock × List BusBlock :=
  let rows := List.zip tables tableLogHeights
  (rows.flatMap fun (t, h) ↦ t.flushes.push.map fun c ↦ ⟨h, c, t.opcode⟩,
    rows.flatMap fun (t, h) ↦ t.flushes.pull.map fun c ↦ ⟨h, c, t.opcode⟩,
    rows.flatMap fun (t, h) ↦ t.countColumns.map fun l ↦ ⟨h, [Form.col l], t.opcode⟩)

/-- The Flock slot of a global column that is an embedded `BLAKE2S` limb
(`verifier.py:888`). -/
def limbSlot (column : ℕ) : Option ℕ :=
  blake2sSlots.zipIdx.findSome? fun (name?, slot) ↦ name?.bind fun name ↦
    if globalColumnBases.getD opBlake2s 0 + colIdx blake2sColumns name = column then some slot
    else none

/-- Every column's log-size, in global order (`verifier.py:881-884`). -/
def columnKappas (logMemory logBytecode : ℕ) (tableLogHeights : List ℕ) : List ℕ :=
  let qflockKappa := tableLogHeights.getD opBlake2s 0 + qflockSlotBits
  [logMemory, logMemory, logMemory, logMemory, logBytecode, qflockKappa] ++
    tables.flatMap fun t ↦ List.replicate t.width (tableLogHeights.getD t.opcode 0)

/-- The placements of every column, and the stack's log-size (`verifier.py:886-896`): the
committed columns stacked by `stack_offsets`, each limb at `q_flock`'s offset plus its slot. -/
def placementsOf (kappas : List ℕ) : List Placement × ℕ :=
  let blockCols := (List.range kappas.length).filter fun c ↦ (limbSlot c).isNone
  let (blockOffsets, totalLog) := stackOffsets (blockCols.map (kappas.getD · 0))
  let offsetOf := fun c ↦ blockOffsets.getD (blockCols.idxOf c) 0
  let placements := kappas.zipIdx.map fun (kappa, column) ↦
    match limbSlot column with
    | some slot =>
      ({ vars := kappa, index := offsetOf qflock + slot, low := qflockSlotBits } : Placement)
    | none => { vars := kappa, index := offsetOf column }
  (placements, max minStackedLog totalLog)

/-- `build_layout(bytecode, log_memory, table_log_heights)` (`verifier.py:858-897`); `none`
where the Python raises. -/
def buildLayout (bytecode : List K) (logMemory : ℕ) (tableLogHeights : List ℕ) : Option Layout :=
  match log2Strict bytecode.length with
  | none => none
  | some logLength =>
    if busBits ≤ logLength ∧ 16 ≤ logMemory ∧ logMemory ≤ 32 ∧
        tableLogHeights.all (· ≤ 32) ∧ 3 ≤ tableLogHeights.getD opBlake2s 0 ∧
        logLength - busBits ≤ 32 ∧ tableLogHeights.length = tables.length then
      let logBytecode := logLength - busBits
      let (push, pull, count) := busBlocks tableLogHeights
      let (placements, stackLog) :=
        placementsOf (columnKappas logMemory logBytecode tableLogHeights)
      some ⟨logMemory, logBytecode, bytecode, push, pull, count, placements, stackLog,
        tableLogHeights⟩
    else none

end
end LeanerVM.Protocol.Verifier
