# Status: end-to-end soundness and completeness of the deployed verifier

Local branch `e2e/rom-knowledge-soundness` (not pushed), built on the open stack #86–#99, #82/#83
and #67. Design: [e2e-rom-design.md](e2e-rom-design.md). Every theorem below depends only on
`propext`, `Classical.choice`, `Quot.sound` (`#print axioms`, locked in the tests).

## The verifier the theorems are about

`LeanerVM.Protocol.Verifier.verify` (`LeanerVM/Protocol/Verifier/Verify.lean`): the compiled
reading, at BLAKE2s, of `leanVmProgram`, a transcription of `python-verifier/verifier.py` at
leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2` in the verifier language
`LeanerVM/Protocol/Compile/Prog.lean` (read, sample, grind, commit, query). Its compiled reading
(`Compile/Run.lean`) is the Fiat–Shamir chain with proof of work and Merkle openings of the
Python. Evidence that the transcription is the Python's: differential tests of every pure helper
and a full replay of a Python mock prover's transcript (`tests/LeanerVMTests/Protocol/Verifier/`,
drivers in `scripts/verifier-mock/`). No proof from the Rust prover is available as a fixture.

## Soundness (`LeanerVM/Protocol/EndToEnd/Sound/Theorem.lean`)

In the random-oracle model for BLAKE2s-256 on byte strings (VCVio's `randomOracle`), against any
adversary making at most `Q_A` queries, with the compiled verifier making at most `13300`
(`Verifier/Cost.lean`):

* `leanVm_romSound`: the verifier accepts while its run is doomed with probability at most
  `(Q_A + 13300)·(2^-128 + 6·(Q_A + 13300)/2^256)` (`failBound`: `(4 + k)·N/2^256` with `k = 2` seeding steps);
* `leanVm_knowledge`: the same bound for "the verifier accepts and the extractor (reading the
  announced sizes and the stack's commitment off the oracle's log, then picking a stack of the
  Johnson list satisfying the relation; a classical choice) returns no stack satisfying
  `M3Holds` of the leanISA instance at admissible sizes";
* `leanVm_execution`: for well-formed bytecode, the same bound for "accepts and the extracted
  witness represents no valid execution" (`ValidExecution`, through the adaptor and leanISA's
  `constraintSoundness`);
* `leanVm_bound_le`: for `Q_A ≤ 2^64` the bound is at most `2^-63`.

The per-query error `2^-128` is certified: every group of challenges of the deployed opening
escapes with probability at most `2^-128` after its 17 bits of proof of work, at all 56
admissible (stack size, rate) pairs (`Whir/Params/Deployed.lean`, a kernel-checked certificate
table over ArkLib's proved Johnson-range MCA; the weakest shape, μ = 16 at rate 3, is at
`2^-128.43`, and `2^-129` is not reachable with the deployed query table). The front phases'
groups are below `2^-150`.

**Open input**: the theorems are parametric in `TableFidHyp prog input`, the equality of the
deployed table sumcheck's computations with the ArkLib model's for leanISA; being discharged
(`Front/TableFidLeanIsa*.lean`).

## Completeness (`LeanerVM/Protocol/EndToEnd/Completeness.lean`)

* `leanVm_interactiveComplete`: from a witness with `SatisfiedBy` at admissible sizes and a valid
  rate, an honest strategy makes the verifier program accept against every challenge function;
* `leanVm_complete` (every hash function) and `leanVm_complete_blake2s` (the deployed `verify`):
  the compiled honest prover's proof is accepted whenever its proof-of-work searches find nonces
  below the fuel;
* `leanVm_complete_of_execution`: from a valid execution of well-formed bytecode that fits
  (`constraintCompleteness`).

## Trust boundary

* BLAKE2s-256 is modelled as a random oracle; nothing is claimed about attacks using its code.
* The statement is non-adaptive: the program and the public input are fixed before the oracle.
* The verifier is the Lean transcription of the Python verifier; its agreement with the Python is
  test evidence (above), its agreement with the Rust verifier is not checked.
* Knowledge extraction is information-theoretic (a classical choice in the Johnson list).

## Findings along the way

* **Model fidelity (fixed)**: the Clean DEREF table flushed its memory reads in the order ptr,
  local, target; the deployed verifier uses ptr, target, local (`tables.rs:637-642`), which
  matters for the bus's leaf stacking. Fixed at the source (`Arithmetization/Tables/Deref.lean`).
* **Roadmap statements**: `no_row_at_sentinel` as written over `w.interactions` is false (the
  verifier's own sentinel pull); proved over the tables' rows. The blueprint's
  `constraintCompleteness` shape was already corrected by #82.
* **Own design**: a first `Spec.bind` rule double-counted returns outside doom (checked
  counterexample); fixed by folding the follower's lead into the potential. Three gaps of the ROM
  design note (groups without a squeeze, the root's own entry, seeding injectivity) were fixed
  as built.
* No soundness or completeness bug of the deployed verifier was found: the WHIR gluing order, the
  OOD and query ordering, the Flock walk (row for row), the public-input check and the bus and
  table computations all match the analysed protocol.
