/-
  LeanerVM.Protocol.Verifier.Arith

  The field and multilinear helpers of leanVM's Python verifier, as pure functions on `E`: the
  integer embeddings, powers, the equality kernel, multilinear and Horner evaluation, the index
  multilinear, the barycentric weights of the Flock skip domain, and the logarithm helpers.
-/

module

public import LeanerVM.Parameters.Flock

/-!
# Verifier arithmetic

Category B: transcribed from `python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, lines 180-315 and 1091-1123. Every function has the
Python's name in `lowerCamelCase` and computes the same value on the inputs the verifier gives it;
the products and sums are taken in the Python's order where it is visible (`foldl` from `1` or
`0`), although `E` is a field and the order does not change a value.

## Conventions

* The Python's `E(n)` for an integer `n < 2^64` is `eOfNat n`, the word `n` in limb `0`: the
  natural-number cast of `E` is the characteristic-two one (`(2 : E) = 0`) and is never used for
  a wire integer. `GEN = E(2)` is `gen`, the element `x` of `K`; `yE` is `E(0, 1)`, the tower
  generator `y`.
* `int(e)` of an `E` element is `eToNat e`, its three limbs as one 192-bit integer
  (`verifier.py:125-126`).
* A `K` value that the Python lifts into `E` (`E.lift`) is `ofK`.

## Preconditions the Python checks and the verifier always meets

`multilinear_eval` requires a table of `2^|point|` entries and `eq_eval`/`dot` zip strictly.
At every call site of the verifier the lengths agree by construction (the table sizes are
`2^k` for the `k` coordinates the caller passes), so these functions are total here: an excess
entry is ignored, as `zip` ignores it.
-/

namespace LeanerVM.Protocol.Verifier

open LeanerVM.Parameters

@[expose] public section

/-! ## Integers and constants -/

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

/-! ## Powers and multilinear helpers -/

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

/-! ## The Flock skip domain (`verifier.py:1091-1123`) -/

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

end
end LeanerVM.Protocol.Verifier
