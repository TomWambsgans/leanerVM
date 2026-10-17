# TODO

## Completeness size cap

`LeanVM.completeness` assumes at most `2^19` steps, `2^23` words of memory and `2^23`
instructions. The deployed verifier admits more: its only limit is a commitment of
`2^28` cells (`MAX_MU = 28`). The cap of `2^19` is forced only by runs made entirely of
`BLAKE2S` steps, each of which costs about 275 cells. A run with few `BLAKE2S` steps
could have about six million steps. Replace the step bound with a condition that counts
`BLAKE2S` steps separately.

## The aggregation guest accepts any bus tiling

`verify_sub` (`lean_ethereum.py:1484-1511`) checks the hinted `sort_order` of the bus blocks
only as a permutation of each side's blocks. The verifier, Lean and Rust, fixes the order
(largest first, ties by index: `stackOffsets`, `bus.rs:59`). So the guest accepts proofs
`verifyDeferred` rejects, and "a valid execution of the guest gives `NodeSpec`" is false as
stated. Fix upstream by checking the order in the guest, as `certify_placement` already does.

## `Spec/Node.lean` against Rust

The digests (statement, signer set, key and SPHINCS lists, DA list), the batching transcript and
`fixedCells` are transcribed and reviewed, not tested. Check them against vectors from
`rec_aggregation`.
