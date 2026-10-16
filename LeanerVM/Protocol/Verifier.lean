/-
  LeanerVM.Protocol.Verifier

  The leanVM verifier, in one file: `python-verifier/verifier.py` at leanVM
  `127510d14c98ade4e8a97646c44fa7f1ff5e752d`, transcribed into Lean, section by section.
-/

module

public import LeanerVM.Parameters.Whir
public import LeanerVM.Parameters.Blake2s
public import LeanerVM.Parameters.Flock
public import LeanerVM.Protocol.Compile.Run
public import LeanerVM.Protocol.Verifier.Fast.Hash

/-!
# The leanVM verifier

Category B: transcribed from `python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`; every citation `verifier.py:N` below is a line of
that file. The sections follow the Python's:

| Section | `verifier.py` |
|---|---|
| Arithmetic: `eq_kernel`, `multilinear_eval`, `eq_eval`, Lagrange | 180-315, 1091-1123 |
| The layout: tables, flushes, forms, `build_layout` | 285-315, 458-531, 631-897 |
| Sumcheck rounds | 405-412, 419-426 |
| The bus phase: GKR, `verify_bus_balance` | 432-455, 526-593 |
| The table sumcheck | 599-628 |
| WHIR: `derive_config`, `verify_whir`, `verify_stacked_opening` | 900-1086, 1346-1355 |
| Flock and ring switching | 1089-1340 |
| `verify_execution`, the seed, `verify` | 345-349, 631, 1358-1408 |
| Loading the four files: `Proof.load`, `main` | 321-331, 1411-1428 |

**What is imported rather than written here**, as the Python imports `hashlib`:

* the fields `K` (`GF(2^64)`) and `E = K[y]/(y^3 + y + 1)` and their arithmetic
  (`LeanerVM.Parameters.Field`, on CompPoly), and the protocol's constants: the WHIR query table
  (`LeanerVM.Parameters.Whir`), the Flock and BLAKE2s constants;
* BLAKE2s-256 (`LeanerVM.Protocol.Blake2sHash`, compiled on machine words by
  `LeanerVM.Protocol.Verifier.Fast.Hash`);
* the Fiat–Shamir transcript: the verifier is a program `Prog` of the verifier language
  (`LeanerVM.Protocol.Compile.Prog`: read a scalar, sample a challenge, check a proof of work,
  read a Merkle root, open it), and `Compile.runProof` (`LeanerVM.Protocol.Compile.Run`) reads it
  on a proof with any hash function `H`, as the Python's `Transcript` does with BLAKE2s. The same
  program is read in the random-oracle model by the soundness proof.

`verifyWith H bytecode publicInput proof` is the verifier with the hash `H`; `verify` is the
deployed one, with BLAKE2s; `verifyFiles` runs it on the four files.
-/

namespace LeanerVM.Protocol.Verifier

open LeanerVM.Parameters

@[expose] public section

/-!
## Verifier arithmetic

From `verifier.py`, lines 180-315 and 1091-1123. Every function has the
Python's name in `lowerCamelCase` and computes the same value on the inputs the verifier gives it;
the products and sums are taken in the Python's order where it is visible (`foldl` from `1` or
`0`), although `E` is a field and the order does not change a value.

### Conventions

* The Python's `E(n)` for an integer `n < 2^64` is `eOfNat n`, the word `n` in limb `0`: the
  natural-number cast of `E` is the characteristic-two one (`(2 : E) = 0`) and is never used for
  a wire integer. `GEN = E(2)` is `gen`, the element `x` of `K`; `yE` is `E(0, 1)`, the tower
  generator `y`.
* `int(e)` of an `E` element is `eToNat e`, its three limbs as one 192-bit integer
  (`verifier.py:125-126`).
* A `K` value that the Python lifts into `E` (`E.lift`) is `ofK`.

### Preconditions the Python checks and the verifier always meets

`multilinear_eval` requires a table of `2^|point|` entries and `eq_eval`/`dot` zip strictly.
At every call site of the verifier the lengths agree by construction (the table sizes are
`2^k` for the `k` coordinates the caller passes), so these functions are total here: an excess
entry is ignored, as `zip` ignores it.
-/

/-! ### Integers and constants -/

/-- The Python `E(n)`: the 64-bit word `n` in limb `0` (`verifier.py:98-101`). -/
def eOfNat (n : ℕ) : E := ofK (K.ofBits n)

/-- The integer value of a `K` word (`K.__index__`). -/
def kToNat (a : K) : ℕ := a.toBitVec.toNat

/-- `int(e)`: the three limbs of `e` as one 192-bit integer, limb `0` lowest
(`verifier.py:125-126`). -/
def eToNat (e : E) : ℕ :=
  kToNat (e.limb 0) + 2 ^ 64 * kToNat (e.limb 1) + 2 ^ 128 * kToNat (e.limb 2)

/-- `GEN = E(2)`, the generator `x` whose powers index the bytecode and the memory
(`verifier.py:182`). -/
def gen : E := eOfNat 2

/-- `E(0, 1)`, the tower generator `y` with `y^3 = y + 1`. -/
def yE : E := E.ofLimbs 0 1 0

/-- `_gpow(index) = GEN ** index` (`verifier.py:665-666`). -/
def gpow (index : ℕ) : E := gen ^ index

/-- `E.sum(values)`: the sum from `ZERO`, left to right (`verifier.py:121-123`). -/
def sumE (values : List E) : E := values.foldl (· + ·) 0

/-- `reduce(mul, values)` with the product of the empty list `1`. -/
def prodE (values : List E) : E := values.foldl (· * ·) 1

/-! ### Powers and multilinear helpers -/

/-- `acc, acc·base, acc·base², …`, `count` terms. -/
def powersFrom (acc base : E) : ℕ → List E
  | 0 => []
  | count + 1 => acc :: powersFrom (acc * base) base count

/-- `powers(base, count) = [1, base, base², …]`, `count` terms (`verifier.py:185-187`). -/
def powers (base : E) (count : ℕ) : List E := powersFrom 1 base count

/-- `eq_kernel(point)`: the `2^|point|` equality weights, the first coordinate the lowest bit
(`verifier.py:232-236`). -/
def eqKernel (point : List E) : List E :=
  point.foldl (fun out r ↦ out.map (· * (1 + r)) ++ out.map (· * r)) [1]

/-- One fold of `multilinear_eval`: adjacent pairs `(a, b)` become `a·(1 + r) + b·r`. -/
def foldPairs (r : E) : List E → List E
  | a :: b :: rest => (a * (1 + r) + b * r) :: foldPairs r rest
  | _ => []

/-- `multilinear_eval(mle, point)`: the multilinear extension of the table at the point, the
first coordinate folding adjacent entries (`verifier.py:239-244`). A table of the wrong size, which
the Python rejects, never reaches it (see the module note); `0` for an empty result. -/
def multilinearEval (mle point : List E) : E :=
  (point.foldl (fun cur r ↦ foldPairs r cur) mle).headD 0

/-- Python's `int.bit_length` on a natural number. -/
def bitLength (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log2 n + 1

/-- `log2_ceil(value) = (value - 1).bit_length()` (`verifier.py:247-248`). The Python gives `1` at
`value = 0`, which no caller passes (every total is positive); here it is `0`. -/
def log2Ceil (value : ℕ) : ℕ := bitLength (value - 1)

/-- `log2_strict(value)`: the exponent of a power of two, `none` otherwise
(`verifier.py:251-253`). -/
def log2Strict (value : ℕ) : Option ℕ :=
  if 0 < value ∧ value &&& (value - 1) = 0 then some (bitLength value - 1) else none

/-- `eq_eval(left, right) = Π (1 + x + y)` (`verifier.py:256-260`). -/
def eqEval (left right : List E) : E :=
  (List.zipWith (fun x z ↦ 1 + x + z) left right).foldl (· * ·) 1

/-- `dot(left, right) = Σ x·y` (`verifier.py:263-267`). -/
def dot (left right : List E) : E :=
  (List.zipWith (· * ·) left right).foldl (· + ·) 0

/-- `index_mle(point)`: the multilinear extension of `[1, g, g², …]` at an LSB-first point,
`Π (1 + r_i·(1 + g^(2^i)))` (`verifier.py:270-277`). -/
def indexMleFrom (generatorPower : E) : List E → E → E
  | [], acc => acc
  | r :: rs, acc => indexMleFrom (generatorPower ^ 2) rs (acc * (1 + r * (1 + generatorPower)))

/-- `index_mle(point)` (`verifier.py:270-277`). -/
def indexMle (point : List E) : E := indexMleFrom gen point 1

/-- `poly_eval(coefficients, point)`: Horner's rule over the coefficients, constant first
(`verifier.py:280-282`). -/
def polyEval (coefficients : List E) (point : E) : E :=
  coefficients.foldr (fun c acc ↦ acc * point + c) 0

/-- `_selector_point(selector, length)`: the low `length` bits of `selector` as `0/1` elements,
lowest first (`verifier.py:313-314`). -/
def selectorPoint (selector length : ℕ) : List E :=
  (List.range length).map fun bit ↦ eOfNat ((selector >>> bit) % 2)

/-! ### The Flock skip domain (`verifier.py:1091-1123`) -/

/-- `PHI[value]`: the image of the byte `value` under `φ_8`, in `E` (`verifier.py:1092`). -/
def phi (value : ℕ) : E := ofK (Flock.phi8 value)

/-- `_window_denominator(count)`: the inverse of `Π_{0 < k < count} PHI[k]`
(`verifier.py:1102-1109`). -/
def windowDenominator (count : ℕ) : E :=
  (((List.range (count - 1)).map fun k ↦ phi (k + 1)).foldl (· * ·) 1)⁻¹

/-- `lagrange_weights(count, point)`: the barycentric weights of the nodes `PHI[:count]` at
`point`, from prefix and suffix products of the differences (`verifier.py:1112-1118`). -/
def lagrangeWeights (count : ℕ) (point : E) : List E :=
  let differences := (List.range count).map fun k ↦ point + phi k
  let prefixes := differences.scanl (· * ·) 1
  let suffixes := (differences.reverse.scanl (· * ·) 1).reverse
  let denominator := windowDenominator count
  List.zipWith (fun p s ↦ p * s * denominator) (prefixes.take count) (suffixes.drop 1)

/-- `lagrange_interpolate(count, values, point)` (`verifier.py:1121-1122`). -/
def lagrangeInterpolate (count : ℕ) (values : List E) (point : E) : E :=
  dot (lagrangeWeights count point) values

/-!
## The verifier's layout

From `verifier.py`, lines 285-315 (`Placement`, `stack_offsets`,
`_selector_point`), 458-531 (`Form`, `BusBlock`, `BusLayout`, `bus_layout`, `ColumnClaim`), and
631-897 (the constants, `Layout`, `Flushes`, `Table`, the six tables, `build_layout`).

### Representation

* A `Form` is the Python's `dict` from monomials to coefficients, as an association list in
  insertion order: `addScaled` adds into an existing monomial's coefficient and appends a new
  one, as the `dict` does. A monomial is the sorted list of its column indices (`()`, `(i,)`,
  `(i, j)`).
* The Python's column-name lookups `_cols` are `colIdx`, `List.idxOf` on the column-name list;
  every name the tables use is in its list, as the Python's `assert` checks.
* `Table.constraints` is a function of the row's evaluations, as in the Python; only `jump` has
  any (`_jump_constraints`).
* `build_layout` returns `none` exactly where the Python raises: a bytecode whose length is not
  a power of two (`log2_strict`), a bytecode shorter than `2^BUS_BITS` (negative
  `log_bytecode`), the size window, and a list of heights not one per table (the strict `zip`).
-/

/-! ### Constants (`verifier.py:523, 631-645, 681-683, 823-855`) -/

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

/-! ### Placements (`verifier.py:285-315`) -/

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

/-! ### Forms (`verifier.py:458-480`) -/

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

/-! ### Flushes (`verifier.py:686-711`) -/

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

/-! ### The instruction tables (`verifier.py:717-855`) -/

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

/-! ### The bus layout (`verifier.py:482-531`) -/

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

/-! ### `build_layout` (`verifier.py:647-657, 858-897`) -/

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

open LeanerVM.Protocol.Compile

/-!
## Sumcheck rounds

From `verifier.py`, lines 405-412 (`Transcript.sumcheck_round_poly`) and
419-426 (`sumcheck`).

A round polynomial `q(X) = c0 + c1·X + c2·X² + …` of `count` coefficients is sent with one
coefficient left out, which the verifier derives from the running claim:

* plain mode (`eq_factor = None`), `q(0) + q(1) = claim`: the prover sends `c0`, then
  `c2, …, c_{count-1}`; `c1 = claim + Σ_{k ≥ 2} c_k` (characteristic two);
* equality mode (`eq_factor = r`), `(1 + r)·q(0) + r·q(1) = claim`: the prover sends
  `c1, …, c_{count-1}`; `c0 = claim + r·Σ_{k ≥ 1} c_k`.

Every coefficient sent is read (`Prog.read`, the Python's `next_scalar`), so absorbed into the
Fiat–Shamir chain in that order. The round's challenge is sampled after its polynomial, and the
next claim is `q(challenge)`.
-/

/-- Fail on `none`: a pure step the Python performs with a `require` inside. -/
def liftOption {α : Type} : Option α → Prog α
  | none => Prog.fail
  | some a => Prog.ret a

/-- `Transcript.sumcheck_round_poly(count, claim, eq_factor)`: read a round polynomial of `count`
coefficients, deriving the one the claim fixes; its coefficients, constant first
(`verifier.py:405-412`). -/
def sumcheckRoundPoly (count : ℕ) (claim : E) : Option E → Prog (List E)
  | none => do
    let constant ← Prog.readE
    let tail ← Prog.readN (count - 2)
    return constant :: (claim + sumE tail) :: tail
  | some eqFactor => do
    let tail ← Prog.readN (count - 1)
    return (claim + eqFactor * sumE tail) :: tail

/-- `sumcheck(transcript, claim, count, equalities)`: one round per entry of `equalities`, each
reading its polynomial and sampling its challenge; the challenges in order, and the final claim
(`verifier.py:419-426`). -/
def sumcheck (claim : E) (count : ℕ) : List (Option E) → Prog (List E × E)
  | [] => return ([], claim)
  | equality :: equalities => do
    let message ← sumcheckRoundPoly count claim equality
    let challenge ← Prog.sampleE
    let (point, final) ← sumcheck (polyEval message challenge) count equalities
    return (challenge :: point, final)

/-!
## The bus phase

From `verifier.py`, lines 432-455 (`verify_gkr_grand_products`) and
526-593 (`BusResult`, `verify_bus_balance`).

**GKR.** The three trees (push, pull, count) are batched: the roots are read as
`shared, count` (push and pull share their root, which is the balance), and the layers are
walked two at a time, one first when the depth is odd. A layer of `step` levels samples its
combiner, runs an equality-mode sumcheck of `2^step + 1` coefficients over the current point,
reads the three trees' `2^step` children, checks that their products combine to the sumcheck's
claim, and samples the `step` new coordinates. The loop is `gkrLayers`, structural in the
remaining depth.

**Leaf decomposition.** Pure (`accumulateSide`): every side's framework blocks are evaluated
outright, its table blocks accumulate into the owner's form for that side, and the side's total
is the GKR value less the framework and the padding.
-/

/-! ### GKR (`verifier.py:432-455`) -/

/-- The state of the GKR walk: the three trees' values at `point`. -/
structure GkrState where
  /-- The push, pull and count values. -/
  values : List E
  /-- The point the values are at. -/
  point : List E

/-- One step of `step` levels of the GKR walk (`verifier.py:441-452`). -/
def gkrStep (step : ℕ) (s : GkrState) : Prog GkrState := do
  let combiner ← Prog.sampleE
  let claim := polyEval s.values combiner
  let (x, claim) ← sumcheck claim (2 ^ step + 1) (s.point.map some)
  let child0 ← Prog.readN (2 ^ step)
  let child1 ← Prog.readN (2 ^ step)
  let child2 ← Prog.readN (2 ^ step)
  let children := [child0, child1, child2]
  let products := children.map prodE
  Prog.require (claim = polyEval products combiner)
  let y ← Prog.sampleN step
  let values := children.map (multilinearEval · y)
  return ⟨values, y ++ x⟩

/-- The `while layer > 0` loop: one level when the remaining depth is odd, two otherwise. -/
def gkrLayers : ℕ → GkrState → Prog GkrState
  | 0, s => return s
  | 1, s => do
    let s ← gkrStep 1 s
    gkrLayers 0 s
  | n + 2, s =>
    if n % 2 = 1 then do
      let s ← gkrStep 1 s
      gkrLayers (n + 1) s
    else do
      let s ← gkrStep 2 s
      gkrLayers n s

/-- `verify_gkr_grand_products(depth)`: the count root, the GKR point, and the three trees'
values there (`verifier.py:432-455`). -/
def verifyGkrGrandProducts (depth : ℕ) : Prog (E × List E × List E) := do
  let shared ← Prog.readE
  let count ← Prog.readE
  let s ← gkrLayers depth ⟨[shared, shared, count], []⟩
  return (count, s.point, s.values)

/-! ### The leaf decomposition (`verifier.py:526-593`) -/

/-- `BusResult`: the framework columns' claims, the GKR point, each table's form per side
(`forms[table][side]`), and what the tables owe each side. -/
structure BusResult where
  /-- The framework columns' claims. -/
  claims : List ColumnClaim
  /-- The GKR point, which the table sumcheck reuses. -/
  point : List E
  /-- `forms[table][side]`. -/
  forms : List (List Form)
  /-- The three sides' totals. -/
  totals : List E

/-- The three framework fingerprints of a side (`verifier.py:556-568`, `fingerprints`; the
Python hoists `memory_index`, `bytecode_index` and `bytecode_value`, pure values inlined here). -/
def fingerprints (layout : Layout) (weights alphas memory memoryLow bytecodeLow : List E)
    (pc memoryCount bytecodeCount : E) : List E :=
  [dot (weights.take 3) [sepState, pc, gpow 0],
    dot (weights.take 6) ([sepMem, indexMle memoryLow, memoryCount] ++ memory),
    dot (weights.take 3) [sepBytecode, indexMle bytecodeLow, bytecodeCount] +
      multilinearEval (layout.bytecode.map ofK) (bytecodeLow ++ alphas)]

/-- One side of the leaf decomposition (`verifier.py:578-591`): the forms with the side's table
blocks added, and the side's total. -/
def accumulateSide (forms : List (List Form)) (side : ℕ) (blocks : List BusBlock)
    (sideLayout : BusLayout) (frameworkFingerprints sideWeights : List E) (sideBeta : E)
    (point : List E) (treeValue : E) : List (List Form) × E :=
  let frameworkSelectors := sideLayout.framework.map (·.eqAbove point)
  let tableSelectors := sideLayout.tables.map (·.eqAbove point)
  let known := dot frameworkSelectors (frameworkFingerprints.map (sideBeta + ·))
  let betaForm := Form.const sideBeta
  let forms := (List.zip tableSelectors blocks).foldl (fun forms (selector, block) ↦
    forms.modify block.owner fun row ↦ row.modify side fun form ↦
      block.coordinates.zipIdx.foldl
        (fun form (coordinate, slot) ↦
          form.addScaled coordinate (selector * sideWeights.getD slot 0))
        (form.addScaled betaForm selector)) forms
  let onesPadding := sumE (frameworkSelectors ++ tableSelectors) + 1
  (forms, treeValue + known + onesPadding)

/-- `verify_bus_balance(layout)` (`verifier.py:534-593`). -/
def verifyBusBalance (layout : Layout) : Prog BusResult := do
  let frameworkLogRows := [0, layout.logMemory, layout.logBytecode]
  let pushLayout := busLayout frameworkLogRows layout.push
  let pullLayout := busLayout frameworkLogRows layout.pull
  let countLayout := busLayout [] layout.count
  let alphas ← Prog.sampleN busBits
  let weights := eqKernel alphas
  let beta ← Prog.sampleE
  let (countRoot, point, treeValues) ← verifyGkrGrandProducts pushLayout.depth
  Prog.require (countRoot ≠ 0)
  let memoryLow := point.take layout.logMemory
  let bytecodeLow := point.take layout.logBytecode
  let memory ← Prog.readN 3
  let memoryFinal ← Prog.readE
  let bytecodeFinal ← Prog.readE
  let claims : List ColumnClaim :=
    (List.zipWith (fun column value ↦ ⟨column, memoryLow, value⟩) [memory0, memory1, memory2]
      memory) ++
    [⟨memoryFinalCounters, memoryLow, memoryFinal⟩, ⟨bytecodeFinalCounters, bytecodeLow,
      bytecodeFinal⟩]
  let fp := fingerprints layout weights alphas memory memoryLow bytecodeLow
  let finalPc := gpow (2 ^ layout.logBytecode - 1)
  let forms0 : List (List Form) := tables.map fun _ ↦ [{}, {}, {}]
  let (forms1, total0) := accumulateSide forms0 0 layout.push pushLayout (fp (gpow 0) 1 1)
    weights beta point (treeValues.getD 0 0)
  let (forms2, total1) := accumulateSide forms1 1 layout.pull pullLayout
    (fp finalPc memoryFinal bytecodeFinal) weights beta point (treeValues.getD 1 0)
  let (forms3, total2) := accumulateSide forms2 2 layout.count countLayout [] [1] 0 point
    (treeValues.getD 2 0)
  return ⟨claims, point, forms3, [total0, total1, total2]⟩

/-!
## The table sumcheck

From `verifier.py`, lines 599-628 (`table_sumcheck`).

One plain-mode sumcheck of four coefficients per round runs over `max` of the tables'
log-heights. Its challenges, reversed, are the point; a table of log-height `h` weighs the first
`h` coordinates by the equality with the bus point and every later one by the challenge itself
(`tableWeights`). The prover then sends each table's row evaluations, in table order, and the
terminal claim must be `Σ weight · (constraints + forms)`, the constraints batched by a disjoint
range of `constraint_powers` per table and the three sides' forms by `form_powers`. Each
evaluation becomes a claim on its global column at the point's first `h` coordinates.
-/

/-- The tables' weights at the point (`verifier.py:611-615`): coordinate `v` contributes
`1 + equality_point[v] + r_v` to a table taller than `v`, and `r_v` to the others. -/
def tableWeights (heights : List ℕ) (equalityPoint point : List E) : List E :=
  point.zipIdx.foldl (fun weights (challenge, coord) ↦
    let equality := 1 + equalityPoint.getD coord 0 + challenge
    List.zipWith (fun weight height ↦ weight * if coord < height then equality else challenge)
      weights heights) (heights.map fun _ ↦ 1)

/-- The per-table loop of `table_sumcheck` (`verifier.py:617-626`): read each table's row
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
equality_point, target)` (`verifier.py:599-628`). -/
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

/-!
## The WHIR opening

From `verifier.py`, lines 900-1086 (`derive_config`, `_ext_row`,
`sample_queries`, `_enforced_sum`, `_subspace_roots`, `_induced_weight`, `GluedClaim`,
`verify_whir`) and 1346-1355 (`verify_stacked_opening`).

### Commitments in the verifier language

The Python reads a Merkle root as two scalars (`Digest.from_halves(*next_scalars(2))`) and opens
it a level later with `merkle(root, block_length, queries, leaf_words)`. The language's
`commit height width` fixes the matrix shape when the root is read, so the shape is computed from
the ladder there:

* the stack's root (commitment `0`, read by `verify_execution` before the bus phase,
  `commitStack`) is opened at level `0`: `2^(log_n − folds[0] + rate_0)` leaves of
  `2^folds[0]` words;
* the root read at level `ℓ` (commitment `ℓ + 1`) is opened at level `ℓ + 1`:
  `2^(message_log_ℓ − folds[ℓ+1] + rate_{ℓ+1})` leaves of `3 · 2^folds[ℓ+1]` words.

Level `ℓ` therefore opens commitment `ℓ` (`Prog.queryP ℓ`). The rows come back as raw words; the
level-0 reversal and the regrouping of deeper rows into `E` (`_ext_row`) are the program's.

### Interpretation

* `derive_config` is `LeanerVM.Parameters.Whir.ladder`, whose `shape` is the Python's loop and
  whose table is `WHIR_QUERIES` verbatim; the tests compare all 56 admissible pairs with the
  Python.
* `sample_queries` takes the block's log-length `depth` (the Python takes the length and recovers
  `depth` by `log2_strict`, which cannot fail: the length is `2^depth`). Its loop is bounded by
  `count` rounds of fuel; each round yields `min(192 / depth, remaining) ≥ 1` positions since
  `depth ≤ 64`.
* `_induced_weight` requires `len(point) == message_log`. Every glued claim is evaluated at
  `folds[fold_start:] + tail_folds`, of length `log_n − fold_start = message_log`, so the check
  always holds; it is not repeated.
* The `raise` after the level loop (no terminal level) is `Prog.fail` on an empty ladder, which
  `derive_config` never returns.
-/

/-! ### Configuration and queries -/

/-- `derive_config(log_n, log_inv_rate)`: the ladder of levels, `none` outside the window
(`verifier.py:922-937`). -/
def deriveConfig (logN logInvRate : ℕ) : Option (List Whir.Level) := Whir.ladder logN logInvRate

/-- The loop of `sample_queries`: each sample yields up to `192 / depth` positions of `depth`
bits, low bits first (`verifier.py:945-953`). -/
def sampleQueriesAux (depth : ℕ) : ℕ → ℕ → Prog (List ℕ)
  | 0, _ => return []
  | fuel + 1, remaining =>
    if remaining = 0 then return []
    else do
      let bits := eToNat (← Prog.sampleE)
      let n := min (192 / depth) remaining
      let chunk := (List.range n).map fun c ↦ (bits >>> (c * depth)) % 2 ^ depth
      let rest ← sampleQueriesAux depth fuel (remaining - n)
      return chunk ++ rest

/-- `sample_queries(transcript, 2^depth, count)` (`verifier.py:945-953`). -/
def sampleQueries (depth count : ℕ) : Prog (List ℕ) := sampleQueriesAux depth count count

/-- `_ext_row(words)`: a deeper level's leaf words regrouped into the `E` values they encode,
three per lane (`verifier.py:940-942`). -/
def extRow : List K → List E
  | c0 :: c1 :: c2 :: rest => E.ofLimbs c0 c1 c2 :: extRow rest
  | [c0, c1] => [E.ofLimbs c0 c1 0]
  | [c0] => [E.ofLimbs c0 0 0]
  | [] => []

/-- `_enforced_sum(rows, folds, query_weights)`: `Σ_q w_q · ⟨row_q, eq(folds, ·)⟩`
(`verifier.py:956-961`). -/
def enforcedSum (rows : List (List E)) (folds queryWeights : List E) : E :=
  let laneWeights := eqKernel folds
  (List.zip queryWeights rows).foldl (fun total (w, row) ↦ total + w * dot row laneWeights) 0

/-- The layers of `_subspace_roots`: square-and-shift the layer by the last root, pop the next
root (`verifier.py:967-969`). -/
def subspaceRootsAux : ℕ → E → List E → List E
  | 0, _, _ => []
  | n + 1, last, layer =>
    match layer.map fun value ↦ value ^ 2 + last * value with
    | [] => []
    | root :: rest => root :: subspaceRootsAux n root rest

/-- `_subspace_roots(log_n)`: `1`, then the `log_n` subspace polynomial values
(`verifier.py:964-970`). -/
def subspaceRoots (logN : ℕ) : List E :=
  1 :: subspaceRootsAux logN 1 ((List.range logN).map fun i ↦ eOfNat (2 ^ (i + 1)))

/-- `_induced_weight(message_log, queries, query_weights, point)`: the level's batched query
claims as one weight at `point`, `Σ_q w_q Π_k (1 + p_k (1 + Ŵ_k(x_q)))`
(`verifier.py:973-991`). -/
def inducedWeight (messageLog : ℕ) (queries : List ℕ) (queryWeights point : List E) : E :=
  let roots := subspaceRoots messageLog
  let inverses := roots.map fun value ↦ if value = 0 then 0 else value⁻¹
  (List.zip queryWeights queries).foldl (fun total (weight, query) ↦
    let product := point.zipIdx.foldl (fun (acc : E × E) (challenge, coordinate) ↦
      (acc.1 * (1 + challenge * (1 + acc.2 * inverses.getD coordinate 0)),
        acc.2 ^ 2 + roots.getD coordinate 0 * acc.2)) (weight, eOfNat query)
    total + product.1) 0

/-- `GluedClaim`: a claim folded into the running sumcheck, and the weight it owes back
(`verifier.py:994-1005`). -/
structure GluedClaim where
  /-- The power of the level's `λ` it was glued with. -/
  scalar : E
  /-- How many fold challenges preceded the level. -/
  foldStart : ℕ
  /-- Its weight at the terminal point, restricted to the level's message coordinates. -/
  weightAt : List E → E

/-! ### The level loop (`verifier.py:1008-1086`) -/

/-- The running state of `verify_whir`. -/
structure WhirState where
  /-- `running_target`. The Python of `127510d1` sets it only in the final level's tail rounds,
  which overwrite the value threaded here, every final message log being at least `2`. -/
  target : E
  /-- `running_quad`. -/
  quad : List E
  /-- Every fold challenge so far. -/
  folds : List E
  /-- The glued claims so far. -/
  glued : List GluedClaim

/-- A level's fold rounds: sample, fold the running claim, read the next quadratic
(`verifier.py:1020-1024`). Returns the state and the level's own challenges. -/
def foldRounds : ℕ → WhirState → List E → Prog (WhirState × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    let challenge ← Prog.sampleE
    let target := polyEval s.quad challenge
    let quad ← sumcheckRoundPoly 3 target none
    foldRounds n { s with target, quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge])

/-- The final level's tail rounds: sample, fold, and read the next quadratic unless it is the
last round (`verifier.py:1067-1073`). The tail challenges and the final running claim. -/
def tailRounds : ℕ → E → List E → Prog (List E × E)
  | 0, target, _ => return ([], target)
  | n + 1, _, quad => do
    let challenge ← Prog.sampleE
    let target := polyEval quad challenge
    if n = 0 then return ([challenge], target)
    else do
      let quad ← sumcheckRoundPoly 3 target none
      let (rest, target) ← tailRounds n target quad
      return (challenge :: rest, target)

/-- Glue a level's pending claims into the running sumcheck with powers of `λ`, the running claim
keeping `λ⁰` (`verifier.py:1058-1062`, which no longer adds the values to `running_target`). -/
def glue (lam : E) (s : WhirState) (pending : List (E × List E × (List E → E))) : WhirState :=
  (pending.foldl (fun (acc : WhirState × E) (value, intro, weightAt) ↦
    let scalar := acc.2 * lam
    let s := acc.1
    ({ s with quad := List.zipWith (fun q i ↦ q + scalar * i) s.quad intro,
              target := s.target + scalar * value,
              glued := s.glued ++ [⟨scalar, s.folds.length, weightAt⟩] }, scalar)) (s, 1)).1

/-- The shape of the commitment a level opens: `2^(message_log + rate)` leaves of `width`
words, the message log being the one after the level's folds. -/
def levelShape (messageLogBefore : ℕ) (level : Whir.Level) (width : ℕ) : ℕ × ℕ :=
  (messageLogBefore - level.fold + level.logInvRate, width)

/-- One level of `verify_whir` and every level after it (`verifier.py:1018-1086`). `index` is
the level's index, which is also the index of the commitment it opens; `laneFolds` is
`config.folds[0]`. -/
def whirLevels (logN laneFolds : ℕ) (evaluateBasis : List E → E) :
    ℕ → List Whir.Level → WhirState → Prog Unit
  | _, [], _ => Prog.fail
  | index, level :: rest, s => do
    let (s, levelFolds) ← foldRounds level.fold s []
    let messageLog := logN - s.folds.length
    -- The level's claims: the residual on the final level; otherwise the next commitment and
    -- its out-of-domain claim.
    let (residual, pending) ← match rest with
      | [] => do
        let residual ← Prog.readN (2 ^ messageLog)
        pure (residual, ([] : List (E × List E × (List E → E))))
      | next :: _ => do
        let (height, width) := levelShape messageLog next (3 * 2 ^ next.fold)
        Prog.commitP height width
        let oodPoint ← Prog.sampleN messageLog
        let oodValue ← Prog.readE
        let intro ← sumcheckRoundPoly 3 oodValue none
        pure ([], [(oodValue, intro, fun x ↦ eqEval oodPoint x)])
    Prog.grindP Whir.queryGrindingBits
    let queries ← sampleQueries (messageLog + level.logInvRate) level.queries
    let lam ← Prog.sampleE
    let queryWeights := powers lam queries.length
    let words ← Prog.queryP index queries
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let intro ← sumcheckRoundPoly 3 enforced none
    let pending := pending ++
      [(enforced, intro, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glue lam s pending
    match rest with
    | [] => do
      let (tailFolds, target) ← tailRounds messageLog s.target s.quad
      let point := s.folds ++ tailFolds
      let weight := s.glued.foldl
        (fun weight claim ↦
          weight + claim.scalar * claim.weightAt (s.folds.drop claim.foldStart ++ tailFolds))
        (evaluateBasis (point.drop laneFolds ++ point.take laneFolds))
      let terminal := weight * multilinearEval residual tailFolds
      Prog.require (terminal = target)
    | _ :: _ => whirLevels logN laneFolds evaluateBasis (index + 1) rest s

/-- `verify_whir(log_n, log_inv_rate, target, root, evaluate_basis)`, the root being commitment
`0` (`verifier.py:1008-1086`). -/
def verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : Prog Unit := do
  let config ← liftOption (deriveConfig logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevels logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config
    ⟨target, quad, [], []⟩

/-- Read the stack's root (`verify_execution`, step 2, `verifier.py:1375`): commitment `0`, the
shape level `0` opens it at. -/
def commitStack (logN logInvRate : ℕ) : Prog Unit := do
  let config ← liftOption (deriveConfig logN logInvRate)
  match config with
  | [] => Prog.fail
  | level :: _ =>
    let (height, width) := levelShape logN level (2 ^ level.fold)
    Prog.commitP height width

/-- `verify_stacked_opening(root, stack_log, log_inv_rate, claims)`: batch the claims with powers
of one challenge into one WHIR opening (`verifier.py:1349-1355`). -/
def verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim) : Prog Unit := do
  let scales := powers (← Prog.sampleE) claims.length
  verifyWhir stackLog logInvRate (dot scales (claims.map (·.2)))
    fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

/-!
## Flock and ring switching

From `verifier.py`, lines 1089-1340: the constants (`FIXED_CHALLENGES`,
`RING_MAP_SHIFTS`), `verify_flock_zerocheck`, `verify_flock_lincheck`, `blake2s_row_values`,
`blake2s_bilinear`, `verify_flock`, `_phi`, `_ring_weight` and `ring_switch`.

The constants are the repository's `LeanerVM.Parameters.Flock` (`Flock.fixedPoint`,
`Flock.ringShifts`, `Flock.phi8`) and `LeanerVM.Parameters.Blake2s` (`iv`, `sigma`); the tests
check them against the Python's values.

`blake2sRowValues` is the Python's forward walk with its two mutable row vectors as the state of
a `StateM`; the word gadgets (`addW`, `add3W`, `linearRows`) write rows exactly where the Python's
closures do, and return the same output words.
-/

/-! ### Constants -/

/-- `FIXED_CHALLENGES`: the seven fixed coordinates of the zerocheck point
(`verifier.py:1096-1099`). -/
def fixedChallenges : List E := Flock.fixedPoint.toList

/-- `RING_MAP_SHIFTS` (`verifier.py:1307`). -/
def ringMapShifts : List ℕ := Flock.ringShifts.toList

/-! ### The zerocheck (`verifier.py:1125-1149`) -/

/-- `ZerocheckResult`. -/
structure ZerocheckResult where
  /-- The skip challenge. -/
  zSkip : E
  /-- The sumcheck's point. -/
  chi : List E
  /-- The claim on `A·z`. -/
  vA : E
  /-- The claim on `B·z`. -/
  vB : E
  /-- The claim on `C·z`. -/
  vC : E

/-- `verify_flock_zerocheck(log_n)` (`verifier.py:1134-1149`): the point is the seven fixed
coordinates then sampled ones; one univariate skip round over the coset, then quadratic
equality-mode rounds, closed by `v_a, v_b`, with `v_c = running + v_a·v_b`. -/
def verifyFlockZerocheck (logN : ℕ) : Prog ZerocheckResult := do
  let sampled ← Prog.sampleN (logN - flockKSkip - fixedChallenges.length)
  let r := fixedChallenges ++ sampled
  let pCoset ← Prog.readN kBits
  let zSkip ← Prog.sampleE
  let vP := lagrangeInterpolate (2 * kBits) (List.replicate kBits 0 ++ pCoset) zSkip
  let (chi, running) ← sumcheck vP 3 (r.map some)
  let vA ← Prog.readE
  let vB ← Prog.readE
  return ⟨zSkip, chi, vA, vB, running + vA * vB⟩

/-! ### The BLAKE2s row vectors (`verifier.py:1179-1294`) -/

/-- `BLAKE2S_G_LANES` (`verifier.py:194`). -/
def blake2sGLanes : List (ℕ × ℕ × ℕ × ℕ) :=
  [(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15), (0, 5, 10, 15), (1, 6, 11, 12),
    (2, 7, 8, 13), (3, 4, 9, 14)]

/-- `BLAKE2S_IV[word]` as an integer. -/
def blake2sIv (word : ℕ) : ℕ := (iv.toList.getD word 0).toNat

/-- `BLAKE2S_SIGMA[round][position]`. -/
def blake2sSigma (round position : ℕ) : ℕ :=
  ((sigma.toList.getD round (Vector.replicate 16 0)).toList.getD position 0).val

/-- The state of the forward walk: the left and right row vectors. -/
abbrev RowM : Type → Type := StateM (Array E × Array E)

/-- Write row `i` of both vectors. -/
def setRow (i : ℕ) (left right : E) : RowM Unit :=
  modify fun s ↦ (s.1.set! i left, s.2.set! i right)

/-- The column weight at a position. -/
def weightAt (columnWeights : Array E) (i : ℕ) : E := columnWeights.getD i 0

/-- `slots(base)`: the 32 column weights of a word. -/
def slotsW (columnWeights : Array E) (base : ℕ) : Array E :=
  Array.ofFn (n := 32) fun bit ↦ weightAt columnWeights (base + bit)

/-- `literal(value)`: the constant's weight at the set bits of `value`. -/
def literalW (columnWeights : Array E) (value : ℕ) : Array E :=
  Array.ofFn (n := 32) fun bit ↦
    if value.testBit bit then weightAt columnWeights blake2sConstantColumn else 0

/-- `xor(x, y)`. -/
def xorW (x z : Array E) : Array E := Array.zipWith (· + ·) x z

/-- `rotate_right(word, amount)`. -/
def rotateRightW (word : Array E) (amount : ℕ) : Array E :=
  Array.ofFn (n := 32) fun bit ↦ word.getD ((bit + amount) % 32) 0

/-- `add(x, y, carry_base)`: the ripple adder's 31 carry rows; its output word. -/
def addW (columnWeights : Array E) (x z : Array E) (carryBase : ℕ) : RowM (Array E) := do
  let mut carry : E := 0
  let mut output : Array E := #[]
  for bit in List.range 32 do
    if bit < 31 then
      setRow (carryBase + bit) (x.getD bit 0 + carry) (z.getD bit 0 + carry)
    output := output.push (x.getD bit 0 + z.getD bit 0 + carry)
    if bit < 31 then
      carry := carry + weightAt columnWeights (carryBase + bit)
  return output

/-- `add3(x, y, z, base)`: 31 majority rows, then 30 ripple rows; its output word. -/
def add3W (columnWeights : Array E) (x z w : Array E) (base : ℕ) : RowM (Array E) := do
  let mut majority : Array E := #[]
  for bit in List.range 31 do
    setRow (base + bit) (x.getD bit 0 + w.getD bit 0) (z.getD bit 0 + w.getD bit 0)
    majority := majority.push (weightAt columnWeights (base + bit) + w.getD bit 0)
  let rippleBase := base + 31
  let mut carry : E := 0
  let mut output : Array E := #[]
  for bit in List.range 32 do
    let q := if bit = 0 then 0 else majority.getD (bit - 1) 0
    let left := x.getD bit 0 + z.getD bit 0 + w.getD bit 0 + carry
    output := output.push (left + q)
    if 1 ≤ bit ∧ bit ≤ 30 then
      setRow (rippleBase + bit - 1) left (q + carry)
      carry := carry + weightAt columnWeights (rippleBase + bit - 1)
  return output

/-- `linear_rows(values, base)`: the rows `(value, constant)`. -/
def linearRows (columnWeights : Array E) (values : Array E) (base : ℕ) : RowM Unit := do
  for bit in List.range 32 do
    setRow (base + bit) (values.getD bit 0) (weightAt columnWeights blake2sConstantColumn)

/-- The forward walk of `blake2s_row_values` (`verifier.py:1249-1287`). -/
def blake2sWalk (cw : Array E) : RowM Unit := do
  let constant := weightAt cw blake2sConstantColumn
  for (base, length) in [(0, 256), (640, 512), (1152, 128)] do
    for row in List.range length do
      setRow (base + row) (weightAt cw (base + row)) constant
  let mut state : Array (Array E) := Array.replicate 16 (Array.replicate 32 0)
  for word in List.range 8 do
    state := state.set! word (slotsW cw (32 * word))
  for word in List.range 4 do
    state := state.set! (8 + word) (literalW cw (blake2sIv word))
  for (word, base) in [(0, 1152), (1, 1184), (2, 1216), (3, 1248)] do
    state := state.set! (12 + word) (xorW (literalW cw (blake2sIv (4 + word))) (slotsW cw base))
  for roundIndex in List.range 10 do
    for ((laneA, laneB, laneC, laneD), gateIndex) in blake2sGLanes.zipIdx do
      let gate := roundIndex * 8 + gateIndex
      let gateBase := 1280 + 184 * gate
      let a := state.getD laneA #[]
      let b := state.getD laneB #[]
      let c := state.getD laneC #[]
      let d := state.getD laneD #[]
      let mx := slotsW cw (640 + 32 * blake2sSigma roundIndex (2 * gateIndex))
      let my := slotsW cw (640 + 32 * blake2sSigma roundIndex (2 * gateIndex + 1))
      let a1 ← add3W cw a b mx gateBase
      let d1 := rotateRightW (xorW d a1) 16
      let c1 ← addW cw c d1 (gateBase + 61)
      let b1 := rotateRightW (xorW b c1) 12
      let a2 ← add3W cw a1 b1 my (gateBase + 92)
      let d2 := rotateRightW (xorW d1 a2) 8
      let c2 ← addW cw c1 d2 (gateBase + 153)
      let b2 := rotateRightW (xorW b1 c2) 7
      state := ((state.set! laneA a2).set! laneB b2 |>.set! laneC c2).set! laneD d2
  for word in List.range 8 do
    let out := xorW (xorW (state.getD word #[]) (state.getD (word + 8) #[])) (slotsW cw (32 * word))
    linearRows cw out (256 + 32 * word)
  setRow blake2sConstantColumn constant constant

/-- `blake2s_row_values(column_weights)`: `A0·w` and `B0·w` by one forward walk of the circuit
(`verifier.py:1179-1288`). -/
def blake2sRowValues (columnWeights : List E) : Array E × Array E :=
  let size := 2 ^ blake2sR1csLogSize
  ((blake2sWalk columnWeights.toArray).run (Array.replicate size 0, Array.replicate size 0)).2

/-- `blake2s_bilinear(alpha, row_weights, column_weights)`: `e_rowᵀ (A0 + α B0) w_col`
(`verifier.py:1291-1294`). -/
def blake2sBilinear (alpha : E) (rowWeights columnWeights : List E) : E :=
  let (left, right) := blake2sRowValues columnWeights
  dot rowWeights left.toList + alpha * dot rowWeights right.toList

/-! ### The lincheck (`verifier.py:1152-1176`) -/

/-- `verify_flock_lincheck(zc)` (`verifier.py:1152-1176`): eight plain-mode rounds bind the
high column coordinates; the 64 slices `s` close the terminal identity. Returns the claim's
point and the slices. -/
def verifyFlockLincheck (zc : ZerocheckResult) : Prog (List E × List E) := do
  let alpha ← Prog.sampleE
  let skipWeights := lagrangeWeights kBits zc.zSkip
  let chiIn := zc.chi.take flockNumLincheckRounds
  let eRow := (eqKernel chiIn).flatMap fun weight ↦ skipWeights.map (weight * ·)
  let claim := zc.vA + alpha * zc.vB + alpha ^ 2 * zc.vC + alpha ^ 3
  let (roundChallenges, rLc) ←
    sumcheck claim 3 (List.replicate flockNumLincheckRounds none)
  let s ← Prog.readN kBits
  let chiInPrime := roundChallenges.reverse
  let wCol := (eqKernel chiInPrime).flatMap fun weight ↦ s.map (· * weight)
  let terminal := blake2sBilinear alpha eRow wCol +
    alpha ^ 2 * eqEval chiIn chiInPrime * dot skipWeights s +
    alpha ^ 3 * wCol.getD blake2sConstantColumn 0
  Prog.require (terminal = rLc)
  return (chiInPrime ++ zc.chi.drop flockNumLincheckRounds, s)

/-- `verify_flock(log_n)`: the zerocheck, then the lincheck (`verifier.py:1297-1301`). -/
def verifyFlock (logN : ℕ) : Prog (List E × List E) := do
  let zc ← verifyFlockZerocheck logN
  verifyFlockLincheck zc

/-! ### Ring switching (`verifier.py:1304-1340`) -/

/-- `_phi(value, challenges)`: `a ↦ a + f_p · a^(2^shift)`, stage by stage
(`verifier.py:1310-1314`). -/
def phiMap (value : E) (challenges : List E) : E :=
  (List.zip challenges ringMapShifts).foldl
    (fun value (challenge, shift) ↦ value + challenge * value ^ (2 ^ shift)) value

/-- `_ring_weight(r, r_prime, coefficients)`: `Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)`
(`verifier.py:1317-1328`). -/
def ringWeight (r rPrime coefficients : List E) : E :=
  (coefficients.foldl (fun (acc : E × List E) c ↦
    let product := (List.zip acc.2 rPrime).foldl
      (fun product (value, challenge) ↦ product * (1 + value + challenge)) c
    (acc.1 + product, acc.2.map (· ^ 2))) (0, r)).1

/-- The Frobenius coefficients of the drawn map, `Φ(a) = Σ_{k < 64} c_k a^(2^k)`
(`verifier.py:1338`). -/
def ringCoefficients (challenges : List E) : List E :=
  (List.range kBits).map fun k ↦
    ((List.zip challenges ringMapShifts).filter fun (_, s) ↦ k &&& s ≠ 0).foldl
      (fun acc (f, s) ↦ acc * f ^ (2 ^ (k % s))) 1

/-- `ring_switch(point, s)` (`verifier.py:1331-1340`): draw the map, and return the target
`Σ_i g^i Φ(s_i)` and the weight `W(u) = Φ(eq(point, u))` as a function of the opening point. -/
def ringSwitch (point s : List E) : Prog (E × (List E → E)) := do
  let challenges ← Prog.sampleN ringMapShifts.length
  let coefficients := ringCoefficients challenges
  let target := polyEval (s.map (phiMap · challenges)) gen
  return (target, fun rPrime ↦ ringWeight point rPrime coefficients)

open LeanerVM.Semantics LeanerVM.Protocol.Blake2sHash

/-!
## The leanVM verifier

From `verifier.py`, lines 631 (`R1CS_DIGEST`), 1358-1408
(`verify_execution`) and 346-349 (`Transcript.__init__`).

`leanVmProgram bytecode publicInput` is `verify_execution` in the verifier language, one
`Prog` function per phase of the Python:

1. the announced sizes (`readN 8`), their checks and `buildLayout`;
2. the stack's root (`commitStack`, commitment `0`);
3. the bus (`verifyBusBalance`);
4. the table sumcheck (`tableSumcheck`) at the bus point;
5. the public input's binding;
6. Flock (`verifyFlock`);
7. ring switching (`ringSwitch`) and the stacked opening (`verifyStackedOpening`), which runs
   WHIR on every claim.

The program returns `true` where the Python returns; `Transcript.finish`, the check that the
proof is consumed, is `Compile.runProof`'s.

**The seed.** The Fiat–Shamir chain starts at `compress(IV, public_input)`, `IV` the BLAKE2s
hash of `"leanvm" ‖ u64le(32) ‖ R1CS_DIGEST ‖ H(bytecode)`, the bytecode hashed as its
little-endian words. `seedWith H` computes it with any hash; `verifyWith H` is the compiled
reading at `H`; `verify` is the deployed verifier, the `Id` instance at `blake2sBytes`
(`verifyWith_blake2sBytes`, by `rfl`).

**Compilation.** `LeanerVM.Protocol.Verifier.Fast.Hash` compiles `blake2sBytes` with the rotation
on machine words, as `LeanerVM.Parameters.FieldWords` compiles the field arithmetic. Both are
`@[csimp]` lemmas: the definitions here, and the theorems about them, are unchanged.
-/

/-! ### The program -/

/-- The announced sizes, read and checked, and the layout they give
(`verifier.py:1364-1372`): the layout and the WHIR rate exponent. -/
def readSizes (bytecode : List K) : Prog (Layout × ℕ) := do
  let announced ← Prog.readN (2 + tables.length)
  Prog.require (announced.all fun value ↦ value.limb 1 = 0 ∧ value.limb 2 = 0)
  let logMemory := kToNat ((announced.headD 0).limb 0)
  let tableLogs := ((announced.drop 1).take tables.length).map fun value ↦ kToNat (value.limb 0)
  let logInverseRate := kToNat ((announced.getLastD 0).limb 0)
  Prog.require (1 ≤ logInverseRate ∧ logInverseRate ≤ 4)
  let layout ← liftOption (buildLayout bytecode logMemory tableLogs)
  Prog.require (minStackedLog ≤ layout.stackLog ∧ layout.stackLog ≤ maxStackedLog)
  return (layout, logInverseRate)

/-- Step 4, the table sumcheck at the bus point (`verifier.py:1380-1388`): the claims of the bus
and of the tables. -/
def tablePhase (layout : Layout) (bus : BusResult) : Prog (List ColumnClaim) := do
  let xi ← Prog.sampleE
  let nConstraints := (tables.map Table.nConstraints).sum
  let xiPowers := powers xi (nConstraints + 3)
  let constraintPowers := xiPowers.take nConstraints
  let formPowers := xiPowers.drop nConstraints
  let target := dot formPowers bus.totals
  let tableClaims ← tableSumcheck layout.tableLogHeights bus.forms constraintPowers formPowers
    bus.point target
  return bus.claims ++ tableClaims

/-- Step 5, binding the public input (`verifier.py:1390-1396`): a challenge, and claims on the
three memory columns at `(challenge, 0, …, 0)`, each limb's claim the line through that limb of
the public input's two halves, evaluated at the challenge by the verifier itself. The prover sends
nothing. -/
def publicInputPhase (layout : Layout) (publicInput : Digest) : Prog (List ColumnClaim) := do
  let publicChallenge ← Prog.sampleE
  let halves := digestScalars publicInput
  let publicLimbs := ([0, 1, 2] : List (Fin 3)).map fun limb ↦
    multilinearEval [ofK (halves.1.limb limb), ofK (halves.2.limb limb)] [publicChallenge]
  let publicPoint := publicChallenge ::
    List.replicate ((layout.placements.getD memory0 default).vars - 1) 0
  return List.zipWith (fun column value ↦ ⟨column, publicPoint, value⟩)
    [memory0, memory1, memory2] publicLimbs

/-- Step 7's ring-switching claim on the stack: supported on `q_flock`'s region, its weight
carries the placement's selector (`verifier.py:1405-1406`). -/
def ringSwitchClaim (layout : Layout) (target : E) (weight : List E → E) : StackClaim :=
  let qflockPlacement := layout.placements.getD qflock default
  (fun x ↦ qflockPlacement.eqAbove x * weight (x.take qflockPlacement.vars), target)

/-- `verify_execution(bytecode, public_input, proof)` without its `finish`
(`verifier.py:1358-1407`). -/
def verifyExecution (bytecode : List K) (publicInput : Digest) : Prog Unit := do
  -- 1] memory log-size, table log-sizes, and the WHIR rate
  let (layout, logInverseRate) ← readSizes bytecode
  -- 2] the stack's commitment
  commitStack layout.stackLog logInverseRate
  -- 3] the bus
  let bus ← verifyBusBalance layout
  -- 4] the table sumcheck
  let claims ← tablePhase layout bus
  -- 5] the public input
  let publicClaims ← publicInputPhase layout publicInput
  let claims := claims ++ publicClaims
  -- 6] BLAKE2s validity via Flock
  let (flockPoint, flockS) ←
    verifyFlock (blake2sR1csLogSize + layout.tableLogHeights.getD opBlake2s 0)
  -- 7] ring switching, then one opening of the stack for every claim
  let (ringTarget, ringWeight) ← ringSwitch flockPoint flockS
  verifyStackedOpening layout.stackLog logInverseRate
    (ringSwitchClaim layout ringTarget ringWeight :: claims.map (·.onStack layout))

/-- **The leanVM verifier program**: `verify_execution` in the verifier language, accepting
where the Python returns. -/
def leanVmProgram (bytecode : List K) (publicInput : Digest) : Prog Bool := do
  verifyExecution bytecode publicInput
  return true

/-! ### The seed and the compiled verifier -/

/-- `R1CS_DIGEST` (`verifier.py:631`). -/
def r1csDigest : List UInt8 :=
  [0x53, 0x7a, 0xd2, 0x07, 0x90, 0x30, 0x8f, 0x8e, 0xb8, 0xc0, 0xe8, 0xbd, 0x3e, 0x6c, 0x58, 0xee,
    0x64, 0x57, 0x33, 0x71, 0xe3, 0xd5, 0x3c, 0x30, 0x61, 0x3d, 0xd0, 0x4d, 0x87, 0xc0, 0xb7, 0xea]

/-- The IV's preimage, `"leanvm" ‖ u64le(len R1CS_DIGEST) ‖ R1CS_DIGEST ‖ H(bytecode)`
(`verifier.py:1360`). -/
def ivPreimage (bytecodeHash : Digest) : Bytes :=
  [0x6c, 0x65, 0x61, 0x6e, 0x76, 0x6d] ++ [32, 0, 0, 0, 0, 0, 0, 0] ++ r1csDigest ++
    digestBytes bytecodeHash

section Hash

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- The chain's initial state with the hash `H`: `compress(IV, public_input)`, the IV being the
hash of `ivPreimage` (`verifier.py:1359-1362`, `Transcript.__init__`). -/
def seedWith (bytecode : List K) (publicInput : Digest) : m Digest := do
  let bytecodeHash ← H (bytecode.flatMap kBytes)
  let fiatShamirIv ← H (ivPreimage bytecodeHash)
  H (digestBytes fiatShamirIv ++ digestBytes publicInput)

/-- The compiled verifier with the hash `H`: the program run on the proof from the seed. -/
def verifyWith (bytecode : List K) (publicInput : Digest) (π : Proof) : m Bool := do
  let seed ← seedWith H bytecode publicInput
  runProof H (leanVmProgram bytecode publicInput) seed π

end Hash

/-- The deployed seed, with BLAKE2s. -/
def seed (bytecode : List K) (publicInput : Digest) : Digest :=
  Id.run (seedWith blake2sBytes bytecode publicInput)

/-- **The deployed leanVM verifier**: the program's compiled reading with BLAKE2s, from the
deployed seed. -/
def verify (bytecode : List K) (publicInput : Digest) (π : Proof) : Bool :=
  Id.run (runProof blake2sBytes (leanVmProgram bytecode publicInput) (seed bytecode publicInput) π)

/-- The deployed verifier is the hash-parametric one at `Id` and BLAKE2s. -/
theorem verifyWith_blake2sBytes (bytecode : List K) (publicInput : Digest) (π : Proof) :
    Id.run (verifyWith blake2sBytes bytecode publicInput π) = verify bytecode publicInput π :=
  rfl

/-!
## Loading a proof from its four files

From `verifier.py`, lines 104-106 (`E.from_bytes`), 203-223 (`Digest`),
321-331 (`Proof.load`), 384-400 (`Transcript._merkle_data`, `Transcript.merkle`) and 1411-1428
(`main`). The pinned Rust prover writes the same files
(`crates/leanvm_core/tests/verifiers/python_verifier.rs`, `python_verify`).

The four files:

* `bytecode.bin`: the bytecode table, 8 little-endian bytes per `K` word (`decodeWords`);
* `public_input.bin`: the 32 bytes of the public input digest (`decodeDigest`);
* `stream.bin`: the scalar stream, 24 bytes per `E` element, its three limbs in order
  (`decodeScalars`);
* `merkle_openings.bin`: every Merkle opening in the order the verifier reads them, each its
  leaf's words (8 bytes each) and then one 32-byte sibling per level, with no length fields.

### Cutting the openings

The Python reads the openings file lazily, `8 · leaf_words` bytes then `32 · height` bytes per
queried position, the shape coming from the commitment it opens. `Proof.openings` is that byte
string already cut (`LeanerVM.Protocol.Compile.Run`, *Deviation*). The cut is computed here from
the verifier's own configuration rather than by a second interpreter of the program: the
announced sizes at the head of the stream, read by the program's own `readSizes`, fix the stack's
log-size and the rate exponent, and `deriveConfig` fixes the WHIR ladder, whose level `ℓ` opens
commitment `ℓ` at `queries_ℓ` positions in the shape `levelShape` gives (`openingShapes`). These
are the only openings the program makes (commitment `0` is the stack, read by `commitStack`; the
others are WHIR's), and `sampleQueries` returns exactly `queries_ℓ` positions.

The cut is sound with no appeal to that argument: `openOne` checks every opening's width and
height against the commitment it is opened against, and `runProof` requires every opening to be
consumed, so `verify` accepts a cut only if it is the one the program reads; and then its bytes
are the Python's reads in order (`encodeOpenings_splitOpenings`, in
`LeanerVM.Protocol.Verifier.Load` with the serializers). It is complete by the round trip
`splitOpenings_encodeOpenings`, given that the shapes are the program's, which the differential
tests on the Rust prover's proofs exercise.
-/

/-! ### Words -/

/-- The word of four little-endian bytes. -/
def wordOfBytes (b0 b1 b2 b3 : UInt8) : UInt32 :=
  UInt32.ofNat (b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat + 2 ^ 24 * b3.toNat)

/-- Read `n` values of `size` bytes each with `decode`, and the bytes after them; `none` if the
bytes run out (checked on the next `size` bytes, not on the length of all the rest). -/
def readMany {α : Type} (size : ℕ) (decode : Bytes → α) : ℕ → Bytes → Option (List α × Bytes)
  | 0, b => some ([], b)
  | n + 1, b =>
    if (b.take size).length = size then
      (readMany size decode n (b.drop size)).map fun r ↦ (decode (b.take size) :: r.1, r.2)
    else none

/-- The `K` word of eight little-endian bytes (`int.from_bytes(…, "little")`). -/
def kOfBytes (b : Bytes) : K :=
  ofWords (wordOfBytes (b.getD 0 0) (b.getD 1 0) (b.getD 2 0) (b.getD 3 0))
    (wordOfBytes (b.getD 4 0) (b.getD 5 0) (b.getD 6 0) (b.getD 7 0))

/-- The digest of 32 bytes, its words little-endian (`Digest`). -/
def digestOfBytes (b : Bytes) : Digest :=
  Vector.ofFn fun j : Fin 8 ↦
    wordOfBytes (b.getD (4 * j) 0) (b.getD (4 * j + 1) 0) (b.getD (4 * j + 2) 0)
      (b.getD (4 * j + 3) 0)

/-- The scalar of 24 bytes, three little-endian limbs (`E.from_bytes`). -/
def eOfBytes (b : Bytes) : E := E.ofLimbs (kOfBytes b) (kOfBytes (b.drop 8)) (kOfBytes (b.drop 16))

/-! ### The files -/

/-- Read exactly the whole of a byte string as values of `size` bytes. -/
def decodeAll {α : Type} (size : ℕ) (decode : Bytes → α) (b : Bytes) : Option (List α) :=
  match readMany size decode (b.length / size) b with
  | some (xs, []) => some xs
  | _ => none

/-- `bytecode.bin`: the bytecode's words (`main`, `verifier.py:1422-1423`). -/
def decodeWords (b : Bytes) : Option (List K) := decodeAll 8 kOfBytes b

/-- `public_input.bin`: the 32-byte public input (`Digest.__post_init__`). -/
def decodeDigest (b : Bytes) : Option Digest :=
  if b.length = 32 then some (digestOfBytes b) else none

/-- `stream.bin`: the scalars (`Proof.load`). -/
def decodeScalars (b : Bytes) : Option (List E) := decodeAll 24 eOfBytes b

/-- Read one opening of the given height and width (`Transcript._merkle_data`). -/
def readOpening (height width : ℕ) (b : Bytes) : Option (Opening × Bytes) := do
  let (leaf, b) ← readMany 8 kOfBytes width b
  let (path, b) ← readMany 32 digestOfBytes height b
  return (⟨leaf, path⟩, b)

/-- Read one opening per shape `(height, width)`, in order. -/
def readOpenings : List (ℕ × ℕ) → Bytes → Option (List Opening × Bytes)
  | [], b => some ([], b)
  | (height, width) :: shapes, b => do
    let (o, b) ← readOpening height width b
    let (os, b) ← readOpenings shapes b
    return (o :: os, b)

/-- Cut the openings file into openings of the given shapes, consuming it. -/
def splitOpenings (shapes : List (ℕ × ℕ)) (b : Bytes) : Option (List Opening) :=
  match readOpenings shapes b with
  | some (os, []) => some os
  | _ => none

/-! ### The shapes the verifier opens -/

/-- The openings of WHIR's levels after the first, the message log before each level's folds
given: `queries` positions of the next commitment's shape (`levelShape`). -/
def laterOpeningShapes : ℕ → List Whir.Level → List (ℕ × ℕ)
  | _, [] => []
  | messageLog, level :: rest =>
    List.replicate level.queries (levelShape messageLog level (3 * 2 ^ level.fold)) ++
      laterOpeningShapes (messageLog - level.fold) rest

/-- The openings of a WHIR run on a `logN`-variable stack, level by level: level `0` opens the
stack at `commitStack`'s shape, level `ℓ + 1` the commitment read at level `ℓ`
(`verify_whir`, `verifier.py:1008-1086`). -/
def whirOpeningShapes (logN : ℕ) : List Whir.Level → List (ℕ × ℕ)
  | [] => []
  | level :: rest =>
    List.replicate level.queries (levelShape logN level (2 ^ level.fold)) ++
      laterOpeningShapes (logN - level.fold) rest

/-- The announced layout and rate exponent of a stream, read by the program's own `readSizes`
(the hash is not consulted for a value: reads only absorb). -/
def announced (bytecode : List K) (stream : List E) : Option (Layout × ℕ) :=
  (Id.run (Compile.run (fun _ ↦ pure default) (readSizes bytecode) ⟨default, stream, [], []⟩)).map
    (·.1)

/-- The shape of every opening `verify` makes on a proof with this stream, in order. -/
def openingShapes (bytecode : List K) (stream : List E) : Option (List (ℕ × ℕ)) := do
  let (layout, logInverseRate) ← announced bytecode stream
  let config ← deriveConfig layout.stackLog logInverseRate
  return whirOpeningShapes layout.stackLog config

/-- The proof in the files `stream.bin` and `merkle_openings.bin`, for this bytecode. -/
def loadProof (bytecode : List K) (stream openings : Bytes) : Option Proof := do
  let scalars ← decodeScalars stream
  let shapes ← openingShapes bytecode scalars
  let openings ← splitOpenings shapes openings
  return ⟨scalars, openings⟩

/-- **The verifier on the four files**: decode them and run `verify`; a file that does not
decode is rejected, as the Python rejects it. -/
def verifyFiles (bytecode publicInput stream openings : Bytes) : Bool :=
  match decodeWords bytecode, decodeDigest publicInput with
  | some words, some digest =>
    match loadProof words stream openings with
    | some π => verify words digest π
    | none => false
  | _, _ => false

end
end LeanerVM.Protocol.Verifier
