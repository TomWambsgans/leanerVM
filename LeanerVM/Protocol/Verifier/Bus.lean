/-
  LeanerVM.Protocol.Verifier.Bus

  The bus phase of leanVM's Python verifier as programs of the verifier language: the batched
  GKR over the push, pull and count grand-product trees, and the leaf decomposition that leaves
  each table a degree-two form and each side a total.
-/

module

public import LeanerVM.Protocol.Verifier.Layout
public import LeanerVM.Protocol.Verifier.Sumcheck

/-!
# The bus phase

Category B: transcribed from `python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, lines 432-455 (`verify_gkr_grand_products`) and
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

namespace LeanerVM.Protocol.Verifier

open LeanerVM.Parameters LeanerVM.Protocol.Compile

@[expose] public section

/-! ## GKR (`verifier.py:432-455`) -/

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

/-! ## The leaf decomposition (`verifier.py:526-593`) -/

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

end
end LeanerVM.Protocol.Verifier
