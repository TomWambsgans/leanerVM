/-
  LeanerVM.Parameters.Isa

  The six opcodes with their bus codes, and the instance caps the verifier checks announced
  sizes against.
-/

module

public import LeanerVM.Parameters.Generator

/-!
# Opcodes and instance caps

leanISA roadmap Layer 2 (`docs/roadmap/leanisa-blueprint.md`). Category B, transcribed at leanVM
pin `127510d14c98ade4e8a97646c44fa7f1ff5e752d`:

* the opcode codes `g^0, …, g^5` in the order XOR, MUL_NATIVE, SET_CONSTANT, DEREF, JUMP,
  BLAKE2S: specification §6.4 (`doc/leanvm/body/06-bus-interactions.tex:95`) and
  `crates/leanvm_core/src/tables.rs:99-104` (`OP_XOR`, …, `OP_BLAKE2S`);
* the memory bounds `16 ≤ κ_mem ≤ 32`: specification §2 (`02-vm-specification.tex:49`) and
  §6.3 (`06-bus-interactions.tex:86`); `crates/leanvm_core/src/cpu/mod.rs:51-52`;
* at most `2^32` rows per table and `2^32` bytecode instructions: specification §6.2, "Instance
  caps" (`06-bus-interactions.tex:80`) and §6.4 (`:93`); `cpu/mod.rs:60` (`MAX_LOG_ROWS`) and
  `crates/verifier/src/layout.rs:84`, `:393` (`MAX_TABLE_LOG`, the bytecode bound);
* at least `2^3` rows in the BLAKE2S table: Flock proves no fewer than eight compressions
  (`crates/flock/src/hash.rs:281-284`, `min_n_blocks_log`), enforced by the verifier at
  `crates/verifier/src/layout.rs:392` and by the filler's `MIN_ROWS`
  (`crates/leanvm_core/src/cpu/filler.rs:43`).

The verifier rejects an announcement outside these caps before any reduction runs
(`crates/verifier/src/layout.rs:387-395`); they are what keeps the total read count below
`2^64 - 1`, the bound the bus argument of Layer 9 needs (specification §6.2). Each cap is a log-2
size, as announced, so that `Program.logSize_le`, Layer 3's `HasPublicBoundary`, and Layer 8's
`Caps` state the verifier's checks by name. The codes are symbolic powers of `g`; the value of `g`
appears only in `LeanerVM.Parameters.Generator`.
-/

namespace LeanerVM.Parameters

@[expose] public section

/-! ## Opcodes -/

/-- The six instructions, in bus-code order (`tables.rs:99-104`). -/
inductive Opcode
  | xor
  | mulNative
  | setConstant
  | deref
  | jump
  | blake2s
  deriving DecidableEq, Repr

/-- The bus code of an opcode: `g^0, …, g^5` in constructor order (specification §6.4). -/
def Opcode.code : Opcode → K
  | .xor => gpow 0
  | .mulNative => gpow 1
  | .setConstant => gpow 2
  | .deref => gpow 3
  | .jump => gpow 4
  | .blake2s => gpow 5

/-- Distinct opcodes have distinct codes. -/
theorem Opcode.code_injective : Function.Injective Opcode.code := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide +kernel)

/-! ## Instance caps -/

/-- The least memory log-size, `2^16` cells (`cpu/mod.rs:51`, `MIN_LOG_MEM`). -/
def minLogMem : ℕ := 16

/-- The greatest memory log-size, `2^32` cells (`cpu/mod.rs:52`, `MAX_LOG_MEM`). -/
def maxLogMem : ℕ := 32

/-- The greatest log-height of an opcode table (`cpu/mod.rs:60`, `MAX_LOG_ROWS`). -/
def maxLogRows : ℕ := 32

/-- The greatest bytecode log-size (`crates/verifier/src/layout.rs:393`; `MAX_LOG_BYTECODE`,
`cpu/mod.rs:64` at `a386121f`, is removed at `127510d1`). -/
def maxLogBytecode : ℕ := 32

/-- The least log-height of the BLAKE2S table, eight rows (`crates/flock/src/hash.rs:281-284`,
`min_n_blocks_log`; `cpu/filler.rs:43`). -/
def minLogRowsBlake2s : ℕ := 3

end
end LeanerVM.Parameters
