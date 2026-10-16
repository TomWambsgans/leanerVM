/-
  LeanerVM.Protocol.Verifier.Flock

  The Flock reduction and ring switching of leanVM's Python verifier as programs of the verifier
  language: the zerocheck with its univariate skip, the lincheck closed by one forward walk of
  the BLAKE2s circuit, and the ring-switching map that turns the 64 slice claims into one claim
  on the stack.
-/

module

public import LeanerVM.Parameters.Blake2s
public import LeanerVM.Protocol.Verifier.Layout
public import LeanerVM.Protocol.Verifier.Sumcheck

/-!
# Flock and ring switching

Category B: transcribed from `python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, lines 1089-1340: the constants (`FIXED_CHALLENGES`,
`RING_MAP_SHIFTS`), `verify_flock_zerocheck`, `verify_flock_lincheck`, `blake2s_row_values`,
`blake2s_bilinear`, `verify_flock`, `_phi`, `_ring_weight` and `ring_switch`.

The constants are the repository's `LeanerVM.Parameters.Flock` (`Flock.fixedPoint`,
`Flock.ringShifts`, `Flock.phi8`) and `LeanerVM.Parameters.Blake2s` (`iv`, `sigma`); the tests
check them against the Python's values.

`blake2sRowValues` is the Python's forward walk with its two mutable row vectors as the state of
a `StateM`; the word gadgets (`addW`, `add3W`, `linearRows`) write rows exactly where the Python's
closures do, and return the same output words.
-/

namespace LeanerVM.Protocol.Verifier

open LeanerVM.Parameters LeanerVM.Protocol.Compile

@[expose] public section

/-! ## Constants -/

/-- `FIXED_CHALLENGES`: the seven fixed coordinates of the zerocheck point
(`verifier.py:1096-1099`). -/
def fixedChallenges : List E := Flock.fixedPoint.toList

/-- `RING_MAP_SHIFTS` (`verifier.py:1307`). -/
def ringMapShifts : List ℕ := Flock.ringShifts.toList

/-! ## The zerocheck (`verifier.py:1125-1149`) -/

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

/-! ## The BLAKE2s row vectors (`verifier.py:1179-1294`) -/

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

/-! ## The lincheck (`verifier.py:1152-1176`) -/

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

/-! ## Ring switching (`verifier.py:1304-1340`) -/

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

end
end LeanerVM.Protocol.Verifier
