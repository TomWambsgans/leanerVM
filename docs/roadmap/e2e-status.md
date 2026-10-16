# Status: end-to-end soundness and completeness of the deployed verifier

Branch `e2e/rom-knowledge-soundness`, built on the open stack #86–#99, #82/#83 and #67, at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`. Design: [e2e-rom-design.md](e2e-rom-design.md).
Every theorem below depends only on `propext`, `Classical.choice`, `Quot.sound` (`#print axioms`,
locked in the tests).

## The front page

[`LeanerVM/Protocol/LeanVM.lean`](../../LeanerVM/Protocol/LeanVM.lean) (namespace `LeanVM`) states
everything on one page, over the semantic types `Program`, `PublicInput`, `ValidExecution`:

* `verifier H prog input proof : m Bool`: the verifier, for a hash function `H : Bytes → m Digest`
  in any monad; `verify` is the BLAKE2s instance (`m = Id`), the deployed verifier, and the
  knowledge-soundness experiment runs the same `verifier` with `H` a random-oracle query;
* `completeness`: if `w` satisfies leanISA's constraint system (`SatisfiedBy`) at admissible
  sizes and a valid rate, the honest proof (`honestProof`) is accepted by `verifier H`, for every
  hash function `H`; `completeness_of_execution` starts from a valid execution;
* `knowledgeSoundness`: for well-formed bytecode and an adversary of at most `Q` queries,
  `Pr[accepted ∧ the extracted witness represents no valid execution] ≤ soundnessError Q`, with
  `soundnessError Q = (Q + 13213)·(2^-128 + 6·(Q + 13213)/2^256)`;
* `soundnessError_le`: at most `2^-63` for `Q ≤ 2^64`.

## The verifier the theorems are about

`verifier` is `LeanerVM.Protocol.Verifier.verifyWith`. The whole verifier is one file,
[`LeanerVM/Protocol/Verifier.lean`](../../LeanerVM/Protocol/Verifier.lean), in the sections of
`verifier.py` (about 1700 lines against the Python's 1433). It is the compiled
reading of `leanVmProgram`, a transcription of `python-verifier/verifier.py` at the pin in the
verifier language `Compile/Prog.lean` (read, sample, grind, commit, query): the Fiat–Shamir chain
with proof of work and Merkle openings. The random-oracle side is the same program,
`verifierComp_leanVm` (`Verifier/Cost.lean`), which makes at most `13213` queries.

**Running it.** `lake exe leanvm-verify bytecode public_input stream merkle_openings`
(`cli/LeanvmVerify.lean`) runs `verify` compiled, on the four files the Rust prover writes. It
checks a real Rust proof in about 0.3–0.7 s and 100 MB: the field (`Parameters/FieldWords.lean`,
`Parameters/CubicExt.lean`) and BLAKE2s (`Verifier/Fast/Hash.lean`) are swapped for word-level
code by `@[csimp]` theorems, so the verifier's definitions are the readable ones and the compiler
runs proven-equal code.

**Evidence that it is the deployed verifier** (test evidence, not proof):

* the pure helpers against the Python, and a full replay of a Python mock prover's transcript
  (`tests/LeanerVMTests/Protocol/Verifier/`, drivers in `scripts/verifier-mock/`);
* three proofs of the Rust prover at the pin (`tests/fixtures/verifier/`, from
  `scripts/export-verifier-fixtures-rust.sh`), accepted;
* differential fuzzing against the deployed Rust verifier (`scripts/fuzz-verifier.py`,
  `scripts/rust-verifier-cli/`): structured and seeded random mutations of every phase's
  scalars, the roots, the nonces, the Merkle openings, the public input and the bytecode; 7500
  cases (seeds 1 and 2 at 250 per fixture, seed 3 at 2000 per fixture), the same verdict every
  time, with every Rust rejection reason the mutations reach exercised and no Rust panic. Seed 3
  runs in about 3 minutes at 8 jobs: `python3 -I scripts/fuzz-verifier.py <leanVM tree>
  tests/fixtures/verifier --mutations 2000 --seed 3 --jobs 8`.

## Soundness (`LeanerVM/Protocol/EndToEnd/Sound/Theorem.lean`)

In the random-oracle model for BLAKE2s-256 on byte strings (VCVio's `randomOracle`), against any
adversary making at most `Q_A` queries:

* `leanVm_romSound`: the verifier accepts while its run is doomed with probability at most
  `(Q_A + 13213)·(2^-128 + failBound)` (`failBound`: `(4 + k)·N/2^256` with `k = 2` seeding
  steps);
* `leanVm_knowledge`: the same bound for "accepts and the extractor (reading the announced sizes
  and the stack's commitment off the oracle's answers, then picking a stack of the Johnson list
  satisfying the relation; a classical choice) returns no stack satisfying `M3Holds`";
* `leanVm_execution`: for well-formed bytecode, the same bound for "accepts and the extracted
  witness represents no valid execution" (through the adaptor and `constraintSoundness`); the
  front page's `knowledgeSoundness` is this statement;
* `leanVm_bound_le`: for `Q_A ≤ 2^64` the bound is at most `2^-63`.

The per-query error `2^-128` is certified: every group of challenges of the deployed opening
escapes with probability at most `2^-128` after its proof of work, at all 56 admissible (stack
size, rate) pairs (`Whir/Params/Deployed.lean`, a kernel-checked certificate table over ArkLib's
proved Johnson-range MCA). The margin is thin: the weakest shape is `(μ, R) = (15, 2)` at about
`2^-128.16`, and `2^-129` is not reachable with the deployed query table. The front phases'
groups are below `2^-150`.

The fold group is proved with the row-union factor `(2·listMax + 2^(ℓ−1)·mcaMax)/|E|`. Annex B at
the pin states the smaller `2L/|E| + ε` (`lem:fold-list`, citing Jo, ePrint 2026/891, Thm 4.4),
under which 25 of the 56 query counts were lowered (`b977f5fa`); the table certifies the lowered
counts under the larger, proved bound, so the Annex's bound is not used.

**No open input.** The theorems take no hypothesis beyond the adversary's query bound (and
well-formed bytecode). The deployed computations of every phase are proved equal to the analysed
protocol's: the bus and the table sumcheck (`Front/TableFidLeanIsa*.lean`), the public input,
Flock and ring switching (`Front/{Pub,Flock,Ring}*.lean`), the BLAKE2s circuit walk row for row
(`Front/WalkFaithful.lean`), and WHIR (`Whir/Sound/`).

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
* The verifier is the Lean transcription of the Python verifier; its agreement with the Python
  and the Rust verifiers is test evidence (above).
* Knowledge extraction is information-theoretic (a classical choice in the Johnson list).

## Findings along the way

* **Model fidelity (fixed)**: the Clean DEREF table flushed its memory reads in the order ptr,
  local, target; the deployed verifier uses ptr, target, local, which matters for the bus's leaf
  stacking. Fixed at the source (`Arithmetization/Tables/Deref.lean`).
* **Roadmap statements**: `no_row_at_sentinel` as written over `w.interactions` is false (the
  verifier's own sentinel pull); proved over the tables' rows. The blueprint's
  `constraintCompleteness` shape was already corrected by #82.
* **Own design**: a first `Spec.bind` rule double-counted returns outside doom (checked
  counterexample); fixed by folding the follower's lead into the potential. Three gaps of the ROM
  design note (groups without a squeeze, the root's own entry, seeding injectivity) were fixed
  as built.
* **Proof interface**: an intermediate hypothesis (`TableFidHyp`) quantified over bus reads with
  any number of fingerprint challenges and was false (with five, the Python's slot weights differ
  from the model's); the deployed verifier always draws four, which the bus specification now
  carries.
* **The bump to `127510d`** (from `a386121f`) changed the verifier, the layout and the parameter
  table; every proof was adapted and the certificate table re-derived. No soundness or
  completeness bug of the deployed verifier was found at either pin: the WHIR gluing order, the
  OOD and query ordering, the Flock walk (row for row), the public-input claims and the bus and
  table computations all match the analysed protocol.
