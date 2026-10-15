/-
  LeanerVM.Protocol.Verifier.Whir

  The WHIR opening of leanVM's Python verifier as programs of the verifier language: the ladder
  configuration, query sampling, the level loop with its commitments, out-of-domain claims,
  proofs of work and Merkle openings, the glued claims and the terminal check, and the stacked
  opening that batches every claim on the stack into one WHIR run.
-/

module

public import LeanerVM.Parameters.Whir
public import LeanerVM.Protocol.Verifier.Layout
public import LeanerVM.Protocol.Verifier.Sumcheck

/-!
# The WHIR opening

Category B: transcribed from `python-verifier/verifier.py` at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, lines 898-1087 (`derive_config`, `_ext_row`,
`sample_queries`, `_enforced_sum`, `_subspace_roots`, `_induced_weight`, `GluedClaim`,
`verify_whir`) and 1353-1362 (`verify_stacked_opening`).

## Commitments in the verifier language

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

## Interpretation

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

namespace LeanerVM.Protocol.Verifier

open LeanerVM.Parameters LeanerVM.Protocol.Compile

@[expose] public section

/-! ## Configuration and queries -/

/-- `derive_config(log_n, log_inv_rate)`: the ladder of levels, `none` outside the window
(`verifier.py:920-935`). -/
def deriveConfig (logN logInvRate : ℕ) : Option (List Whir.Level) := Whir.ladder logN logInvRate

/-- The loop of `sample_queries`: each sample yields up to `192 / depth` positions of `depth`
bits, low bits first (`verifier.py:943-951`). -/
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

/-- `sample_queries(transcript, 2^depth, count)` (`verifier.py:943-951`). -/
def sampleQueries (depth count : ℕ) : Prog (List ℕ) := sampleQueriesAux depth count count

/-- `_ext_row(words)`: a deeper level's leaf words regrouped into the `E` values they encode,
three per lane (`verifier.py:938-940`). -/
def extRow : List K → List E
  | c0 :: c1 :: c2 :: rest => E.ofLimbs c0 c1 c2 :: extRow rest
  | [c0, c1] => [E.ofLimbs c0 c1 0]
  | [c0] => [E.ofLimbs c0 0 0]
  | [] => []

/-- `_enforced_sum(rows, folds, query_weights)`: `Σ_q w_q · ⟨row_q, eq(folds, ·)⟩`
(`verifier.py:954-959`). -/
def enforcedSum (rows : List (List E)) (folds queryWeights : List E) : E :=
  let laneWeights := eqKernel folds
  (List.zip queryWeights rows).foldl (fun total (w, row) ↦ total + w * dot row laneWeights) 0

/-- The layers of `_subspace_roots`: square-and-shift the layer by the last root, pop the next
root (`verifier.py:965-967`). -/
def subspaceRootsAux : ℕ → E → List E → List E
  | 0, _, _ => []
  | n + 1, last, layer =>
    match layer.map fun value ↦ value ^ 2 + last * value with
    | [] => []
    | root :: rest => root :: subspaceRootsAux n root rest

/-- `_subspace_roots(log_n)`: `1`, then the `log_n` subspace polynomial values
(`verifier.py:962-968`). -/
def subspaceRoots (logN : ℕ) : List E :=
  1 :: subspaceRootsAux logN 1 ((List.range logN).map fun i ↦ eOfNat (2 ^ (i + 1)))

/-- `_induced_weight(message_log, queries, query_weights, point)`: the level's batched query
claims as one weight at `point`, `Σ_q w_q Π_k (1 + p_k (1 + Ŵ_k(x_q)))`
(`verifier.py:971-989`). -/
def inducedWeight (messageLog : ℕ) (queries : List ℕ) (queryWeights point : List E) : E :=
  let roots := subspaceRoots messageLog
  let inverses := roots.map fun value ↦ if value = 0 then 0 else value⁻¹
  (List.zip queryWeights queries).foldl (fun total (weight, query) ↦
    let product := point.zipIdx.foldl (fun (acc : E × E) (challenge, coordinate) ↦
      (acc.1 * (1 + challenge * (1 + acc.2 * inverses.getD coordinate 0)),
        acc.2 ^ 2 + roots.getD coordinate 0 * acc.2)) (weight, eOfNat query)
    total + product.1) 0

/-- `GluedClaim`: a claim folded into the running sumcheck, and the weight it owes back
(`verifier.py:992-1003`). -/
structure GluedClaim where
  /-- The power of the level's `λ` it was glued with. -/
  scalar : E
  /-- How many fold challenges preceded the level. -/
  foldStart : ℕ
  /-- Its weight at the terminal point, restricted to the level's message coordinates. -/
  weightAt : List E → E

/-! ## The level loop (`verifier.py:1006-1087`) -/

/-- The running state of `verify_whir`. -/
structure WhirState where
  /-- `running_target`. -/
  target : E
  /-- `running_quad`. -/
  quad : List E
  /-- Every fold challenge so far. -/
  folds : List E
  /-- The glued claims so far. -/
  glued : List GluedClaim

/-- A level's fold rounds: sample, fold the running claim, read the next quadratic
(`verifier.py:1019-1024`). Returns the state and the level's own challenges. -/
def foldRounds : ℕ → WhirState → List E → Prog (WhirState × List E)
  | 0, s, levelFolds => return (s, levelFolds)
  | n + 1, s, levelFolds => do
    let challenge ← Prog.sampleE
    let target := polyEval s.quad challenge
    let quad ← sumcheckRoundPoly 3 target none
    foldRounds n { s with target, quad, folds := s.folds ++ [challenge] }
      (levelFolds ++ [challenge])

/-- The final level's tail rounds: sample, fold, and read the next quadratic unless it is the
last round (`verifier.py:1068-1074`). The tail challenges and the final running claim. -/
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
keeping `λ⁰` (`verifier.py:1058-1063`). -/
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

/-- One level of `verify_whir` and every level after it (`verifier.py:1017-1087`). `index` is
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
`0` (`verifier.py:1006-1087`). -/
def verifyWhir (logN logInvRate : ℕ) (target : E) (evaluateBasis : List E → E) : Prog Unit := do
  let config ← liftOption (deriveConfig logN logInvRate)
  let quad ← sumcheckRoundPoly 3 target none
  whirLevels logN ((config.head?.map (·.fold)).getD 0) evaluateBasis 0 config
    ⟨target, quad, [], []⟩

/-- Read the stack's root (`verify_execution`, step 2, `verifier.py:1382`): commitment `0`, the
shape level `0` opens it at. -/
def commitStack (logN logInvRate : ℕ) : Prog Unit := do
  let config ← liftOption (deriveConfig logN logInvRate)
  match config with
  | [] => Prog.fail
  | level :: _ =>
    let (height, width) := levelShape logN level (2 ^ level.fold)
    Prog.commitP height width

/-- `verify_stacked_opening(root, stack_log, log_inv_rate, claims)`: batch the claims with powers
of one challenge into one WHIR opening (`verifier.py:1356-1362`). -/
def verifyStackedOpening (stackLog logInvRate : ℕ) (claims : List StackClaim) : Prog Unit := do
  let scales := powers (← Prog.sampleE) claims.length
  verifyWhir stackLog logInvRate (dot scales (claims.map (·.2)))
    fun point ↦ dot scales (claims.map fun c ↦ c.1 point)

end
end LeanerVM.Protocol.Verifier
