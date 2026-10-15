/-
  LeanerVM.Protocol.Verifier.Verify

  leanVM's deployed verifier as one program of the verifier language: `verify_execution` of the
  Python verifier, phase by phase, with its Fiat–Shamir seed, and its compiled reading, the
  verifier that runs on a proof.
-/

module

public import LeanerVM.Protocol.Compile.Run
public import LeanerVM.Protocol.Verifier.Bus
public import LeanerVM.Protocol.Verifier.TableSumcheck
public import LeanerVM.Protocol.Verifier.Flock
public import LeanerVM.Protocol.Verifier.Whir

/-!
# The leanVM verifier

Category B: transcribed from `python-verifier/verifier.py` at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, lines 629 (`R1CS_DIGEST`), 1365-1414
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
-/

namespace LeanerVM.Protocol.Verifier

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol.Compile
open LeanerVM.Protocol.Blake2sHash

@[expose] public section

/-! ## The program -/

/-- The announced sizes, read and checked, and the layout they give
(`verifier.py:1371-1379`): the layout and the WHIR rate exponent. -/
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

/-- Step 4, the table sumcheck at the bus point (`verifier.py:1387-1395`): the claims of the bus
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

/-- Step 5, binding the public input (`verifier.py:1397-1402`): two limbs read, checked against
the public input's halves at a challenge, and claimed on the memory columns at
`(challenge, 0, …, 0)`. -/
def publicInputPhase (layout : Layout) (publicInput : Digest) : Prog (List ColumnClaim) := do
  let publicChallenge ← Prog.sampleE
  let limbs ← Prog.readN 2
  let publicLimbs := limbs ++ [0]
  let halves := digestScalars publicInput
  Prog.require
    (polyEval publicLimbs yE = multilinearEval [halves.1, halves.2] [publicChallenge])
  let publicPoint := publicChallenge ::
    List.replicate ((layout.placements.getD memory0 default).vars - 1) 0
  return List.zipWith (fun column value ↦ ⟨column, publicPoint, value⟩)
    [memory0, memory1, memory2] publicLimbs

/-- Step 7's ring-switching claim on the stack: supported on `q_flock`'s region, its weight
carries the placement's selector (`verifier.py:1411-1412`). -/
def ringSwitchClaim (layout : Layout) (target : E) (weight : List E → E) : StackClaim :=
  let qflockPlacement := layout.placements.getD qflock default
  (fun x ↦ qflockPlacement.eqAbove x * weight (x.take qflockPlacement.vars), target)

/-- `verify_execution(bytecode, public_input, proof)` without its `finish`
(`verifier.py:1365-1413`). -/
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

/-! ## The seed and the compiled verifier -/

/-- `R1CS_DIGEST` (`verifier.py:629`). -/
def r1csDigest : List UInt8 :=
  [0x53, 0x7a, 0xd2, 0x07, 0x90, 0x30, 0x8f, 0x8e, 0xb8, 0xc0, 0xe8, 0xbd, 0x3e, 0x6c, 0x58, 0xee,
    0x64, 0x57, 0x33, 0x71, 0xe3, 0xd5, 0x3c, 0x30, 0x61, 0x3d, 0xd0, 0x4d, 0x87, 0xc0, 0xb7, 0xea]

/-- The IV's preimage, `"leanvm" ‖ u64le(len R1CS_DIGEST) ‖ R1CS_DIGEST ‖ H(bytecode)`
(`verifier.py:1367`). -/
def ivPreimage (bytecodeHash : Digest) : Bytes :=
  [0x6c, 0x65, 0x61, 0x6e, 0x76, 0x6d] ++ [32, 0, 0, 0, 0, 0, 0, 0] ++ r1csDigest ++
    digestBytes bytecodeHash

section Hash

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- The chain's initial state with the hash `H`: `compress(IV, public_input)`, the IV being the
hash of `ivPreimage` (`verifier.py:1366-1369`, `Transcript.__init__`). -/
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

end
end LeanerVM.Protocol.Verifier
