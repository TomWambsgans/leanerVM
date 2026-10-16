/-
  LeanerVM.Semantics

  leanISA, the instruction set of leanVM, in one file: the memory, the instructions and programs,
  one step of the machine, and valid executions. What the theorems about the verifier are about.
-/

module

public import LeanerVM.Parameters.Generator
public import LeanerVM.Parameters.Isa
public import LeanerVM.Parameters.Blake2s
public import LeanerVM.Parameters.Field

/-!
# leanISA

The semantics of leanVM's instruction set, written from specification §2
(`doc/leanvm/body/02-vm-specification.tex` at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`).
It is all a reader of the end-to-end theorems (`LeanerVM.Protocol.LeanVM`) needs:

* **memory**: `MemImage κ`, `2^κ` words of `E` at the addresses `g^i`, fixed before the run
  (all nondeterminism is the choice of the image), and the public input in its first two words;
* **programs**: `Instr`, the six instructions, and `Program`, a bytecode of `2^logSize`
  instructions at the addresses `g^i`;
* **one step**: `step prog L r` fetches the instruction at `pc` and checks its relation on the
  words it reads, `none` on a failed fetch, read or check; `BLAKE2S` checks `CompressCells`, the
  RFC 7693 compression on the cells' words;
* **valid executions**: `ValidExecution prog input t`: the memory has `16 ≤ κ ≤ 32` and the
  public input in its first two words, and `t.steps` steps from `(pc, fp) = (1, 1)` reach
  `(g^(N − 1), 1)`, the last bytecode slot, with the frame pointer back at `1`.

`step` and `run` are specifications (`gLog?`, the address-to-index map, is a classical choice).
The lemmas about them are in `LeanerVM.Semantics.Lemmas`; an executable interpreter, proved equal
to `run`, is `LeanerVM.Semantics.Executable`.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

/-!
## The memory image and the public input


**Addressing** (Category B: specification §2, `doc/leanvm/body/02-vm-specification.tex:24` and
`:51-54`). Memory is `2^κ` words of `E`, the word of logical index `i` sits at the address
`g ^ i ∈ K`, and an access at any other address, `0` included, is invalid. `gLog?` is the bounded
discrete logarithm that turns an address back into its index, or `none`; `MemImage.read` is the
only reader. It is `noncomputable`: the index is `Classical.choose` of `∃ i, a = g ^ i`, so the
specification cannot be run, and it is trusted through `gLog?_spec` alone, with its body not
exposed, so a `module` importer can reason about it only through the specification. The cost of
a discrete logarithm never enters the semantics; a computable carrier for running executions, if
one is ever wanted, is separate work bridged to this specification.

**The image** (Category A, roadmap Layer 2, from specification §2 "Write-once memory" and
"Non determinism", `02-vm-specification.tex:39-49`). The memory is committed whole before
execution and every instruction only reads it, so an execution's memory is one total function
`MemImage κ = Fin (2 ^ κ) → E`, and *all* nondeterminism — the log-size `κ` and every
prover-chosen word — is the choice of image. The executor's write-once bookkeeping, zero reads
of unset cells, and on-demand growth (`crates/leanvm_core/src/cpu/execute.rs`) are witness
generation producing such an image, not a second memory model (roadmap acceptance test 19).
Rust-informed: the executor's seeding and address decoding (`execute.rs:143-147`, `:219-221`)
were read before this file was written. `MemImage.limbsAt` and `MemImage.cellAt` read a word
back as a row's limbs (zero when there is none): the vocabulary of Layer 6's row builders,
noncomputable like `read` and specified by `ofLimbs_limbsAt`, `limbsAt_getElem_zero` and
`ofCell_cellAt`; they read, and never a second time differently.

**The public input** (Category B: specification §2, `02-vm-specification.tex:18,26`, and §8.2,
`08-end-to-end-protocol.tex:29`; seeded at `execute.rs:219-221`, a third limb rejected at
`crates/leanvm_core/src/cpu/mod.rs:688-690`, the verifier wrapper). The 256-bit input is four `K`
lanes fixing the first two words of the image as `input₀ + input₁·y` and `input₂ + input₃·y`, top
limbs zero.

### Wrong readings excluded

* `read L 0 = none` for every image and every size (`MemImage.read_zero`; acceptance test 2).
* `gLog?_spec` requires `κ < 64`: with `2 ^ κ > 2 ^ 64 - 1 = orderOf g` one address would name
  two indices. Every announced size has `κ ≤ maxLogMem = 32`, which Layer 3's
  `HasPublicBoundary` carries; the semantics itself imposes no cap.
* `word0` and `word1` take two lanes each, never three (`PublicInput.words_injective`;
  acceptance test 17).
-/

/-! ### Exponent addressing -/

public section

open Classical in
/-- The bounded discrete logarithm: `some i` when `a = g ^ i` with `i < 2 ^ κ`, else `none`.
The index is chosen, not computed, so the specification cannot be run; not exposed, so importers
use it through `gLog?_spec`. -/
noncomputable def gLog? (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  if h : ∃ i : Fin (2 ^ κ), a = gpow i then some (Classical.choose h) else none

/-- The specification of `gLog?`: on an address space of at most `2 ^ 63` cells, so that
`2 ^ κ ≤ orderOf g`, `gLog? κ a = some i` exactly when `a = g ^ i`. -/
theorem gLog?_spec {κ : ℕ} (hκ : κ < 64) {a : K} {i : Fin (2 ^ κ)} :
    gLog? κ a = some i ↔ a = gpow i := by
  unfold gLog?
  split_ifs with h
  · have hc := Classical.choose_spec h
    constructor
    · intro hi
      obtain rfl := Option.some.inj hi
      exact hc
    · intro hi
      have hbound : 2 ^ κ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hj : ((Classical.choose h : Fin (2 ^ κ)) : ℕ) < 2 ^ 64 - 1 := by
        have := (Classical.choose h).isLt; omega
      have hi' : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
      exact congrArg some (Fin.ext (gpow_injOn hj hi' (hc.symm.trans hi)))
  · exact ⟨fun hi ↦ (nomatch hi), fun hi ↦ absurd ⟨i, hi⟩ h⟩

/-- `gLog?` fails exactly on the addresses that are no power below `2 ^ κ`; no size bound is
needed. -/
theorem gLog?_eq_none_iff {κ : ℕ} {a : K} :
    gLog? κ a = none ↔ ∀ i : Fin (2 ^ κ), a ≠ gpow i := by
  unfold gLog?
  split_ifs with h
  · exact ⟨fun hn ↦ (nomatch hn), fun hn ↦ absurd h (not_exists.mpr hn)⟩
  · exact ⟨fun _ ↦ not_exists.mp h, fun _ ↦ rfl⟩

/-- `0` is never an address, whatever the size. -/
theorem gLog?_zero (κ : ℕ) : gLog? κ 0 = none :=
  gLog?_eq_none_iff.mpr fun i h ↦ gpow_ne_zero i h.symm

/-- A power past the end is no address: `g ^ j` with `2 ^ κ ≤ j < orderOf g` has no index. -/
theorem gLog?_gpow_eq_none {κ j : ℕ} (hj : 2 ^ κ ≤ j) (hj' : j < 2 ^ 64 - 1) :
    gLog? κ (gpow j) = none :=
  gLog?_eq_none_iff.mpr fun i h ↦ by
    have hi : (i : ℕ) < 2 ^ 64 - 1 := by have := i.isLt; omega
    have := gpow_injOn hj' hi h
    have := i.isLt
    omega

end

@[expose] public section

/-! ### The memory image -/

/-- The committed memory: `2 ^ κ` words of `E`, by logical index. -/
abbrev MemImage (κ : ℕ) : Type := Fin (2 ^ κ) → E

/-- Read the word at address `a`: `some (L i)` when `a = g ^ i`, `none` otherwise. -/
noncomputable def MemImage.read {κ : ℕ} (L : MemImage κ) (a : K) : Option E :=
  (gLog? κ a).map L

/-- The limbs of the word at `a`, zero when there is none: `read`, read back into a row's
three-limb column (roadmap Layer 6, the row builders). Noncomputable as `read` is; not a
second reader, and specified by `ofLimbs_limbsAt`. -/
noncomputable def MemImage.limbsAt {κ : ℕ} (L : MemImage κ) (a : K) : Vector K 3 :=
  match L.read a with
  | some v => #v[v.limb 0, v.limb 1, v.limb 2]
  | none => #v[0, 0, 0]

/-- The two limbs of the canonical word at `a`, zero when there is none: `read`, read back into
a `BLAKE2S` row's cell column; specified by `ofCell_cellAt`. -/
noncomputable def MemImage.cellAt {κ : ℕ} (L : MemImage κ) (a : K) : Vector K 2 :=
  match L.read a with
  | some v => #v[v.limb 0, v.limb 1]
  | none => #v[0, 0]

/-! ### The public input -/

/-- The 256-bit public input as four `K` lanes (specification §2). -/
structure PublicInput where
  /-- `input₀, …, input₃`. -/
  lanes : Fin 4 → K
  deriving DecidableEq

/-- The first memory word, `input₀ + input₁·y`. -/
def PublicInput.word0 (p : PublicInput) : E := E.ofLimbs (p.lanes 0) (p.lanes 1) 0

/-- The second memory word, `input₂ + input₃·y`. -/
def PublicInput.word1 (p : PublicInput) : E := E.ofLimbs (p.lanes 2) (p.lanes 3) 0

/-!
## Instructions and programs

Category B: the instruction set is specification
§2 (`doc/leanvm/body/02-vm-specification.tex:56-70`, the table; `:73-81`, the `DEREF` store
modes), matching `crates/leanvm_core/src/cpu/isa.rs:6-66` (`Op`, `DerefMode`); the bytecode is
`2 ^ κ_bc` instructions with `κ_bc ≤ 32`, addressed like memory (§2 `:18,24`; §6.4
`06-bus-interactions.tex:93`; `crates/verifier/src/layout.rs:386`, `:393`).

An operand is a `K` element: the `g`-power `o = g ^ j` naming the frame cell at `fp · o` (§2
"Operands and addressing"), except that `SET_CONSTANT`'s immediate is one word `k ∈ E`, whose
three lanes are the operands `k₀, k₁, k₂` of the specification's table (`isa.rs:17-23`, one
`F192`). The executor keeps operands as `u32` exponents (status finding R1); the machine's
operands are the field elements, so an operand that is not a `g`-power is expressible and names
no valid cell.

`Program.fetch` reads the instruction at a program counter through the same bounded logarithm
as memory: `pc = g ^ i` with `i < 2 ^ logSize` fetches instruction `i` and every other `pc`
fetches nothing. The halting test of Layer 3 runs before the fetch, so a valid execution never
fetches the sentinel slot `g ^ (2 ^ logSize - 1)` (roadmap acceptance test 5). `Program` stores
typed `Instr` values, so the store-mode flag pair `(1, 1)` has no constructor. Layer 4
separately specifies canonical encodings and an eight-coordinate entry decoder that rejects
invalid flags (acceptance test 18). `Program.fetch` is an address lookup, not a raw-bytecode
parser; correspondence with raw program loading remains a separate obligation.
-/


/-! ### Instructions -/

/-- The source a `DEREF` stores: the local cell `[o₃]`, the return address `g² · pc`, or `fp`
(specification §2; `isa.rs:58-66`, flags `(f_pc, f_fp) = (0,0), (1,0), (0,1)`). -/
inductive DerefMode
  | cell
  | pc
  | fp
  deriving DecidableEq, Repr

/-- The six instructions with their operands, in the order of the specification's table (§2).
`[o]` is the word at `fp · o`. -/
inductive Instr
  /-- `XOR [o_A, o_B, o_C]`: `[o_C] = [o_A] + [o_B]` in `E`. -/
  | xor (oA oB oC : K)
  /-- `MUL_NATIVE [o_A, o_B, o_C]`: `[o_C] = [o_A] · [o_B]` in `E`. -/
  | mulNative (oA oB oC : K)
  /-- `SET_CONSTANT [o, k₀, k₁, k₂]`: `[o] = k`, the immediate `k = k₀ + k₁·y + k₂·y²`. -/
  | setConstant (o : K) (k : E)
  /-- `DEREF [o₁, o₂, o₃; mode]`: `mem[[o₁] · o₂]` is the source selected by `mode`. -/
  | deref (o1 o2 o3 : K) (mode : DerefMode)
  /-- `JUMP [o_c, o_d, o_f]`: to `([o_d], [o_f])` when `[o_c] ≠ 0`, else fall through. -/
  | jump (oc od of : K)
  /-- `BLAKE2S [o_{m₀}, …, o_{m₃}, o_cv, o_out, o_md]`: the compression of the four message
  cells under the chaining-value pair at `o_cv`, into the pair at `o_out`, with metadata
  `[o_md]`. -/
  | blake2s (om : Fin 4 → K) (ocv oout omd : K)
  deriving DecidableEq

/-- The opcode of an instruction. -/
def Instr.opcode : Instr → Opcode
  | .xor .. => .xor
  | .mulNative .. => .mulNative
  | .setConstant .. => .setConstant
  | .deref .. => .deref
  | .jump .. => .jump
  | .blake2s .. => .blake2s

/-! ### Programs -/

/-- A bytecode of `2 ^ logSize` instructions within the verifier's cap (specification §6.4;
`crates/verifier/src/layout.rs:386`, `:393`); instruction `i` sits at address `g ^ i`. -/
structure Program where
  /-- The bytecode log-size `κ_bc`. -/
  logSize : ℕ
  /-- The cap `κ_bc ≤ 32`. -/
  logSize_le : logSize ≤ maxLogBytecode
  /-- The instructions, by logical index. -/
  code : Fin (2 ^ logSize) → Instr

/-- Fetch the instruction at `pc`: `some (code i)` when `pc = g ^ i`, `none` otherwise
(specification §2, execution loop step 1). -/
noncomputable def Program.fetch (prog : Program) (pc : K) : Option Instr :=
  (gLog? prog.logSize pc).map prog.code

/-!
## BLAKE2s compression and the cell encoding

Category B, in two parts.

**The compression function** is RFC 7693 §3.1 (the mixing function `G`) and §3.2 (the
compression function `F`) with `w = 32`, ten rounds, and rotations `(16, 12, 8, 7)` (§2.1),
extended by the tree-mode *last node* flag of the BLAKE2 specification (Aumasson, Neves,
Wilcox-O'Hearn, Winnerlein, *BLAKE2: simpler, smaller, fast as MD5*, §2.3–§2.4): the reference
implementation `blake2s-ref.c` initialises `v[14] = f[0] ^ IV[6]` and `v[15] = f[1] ^ IV[7]`,
where `f[0]` (last block) and `f[1]` (last node) are 32-bit words equal to `0xFFFFFFFF` when set.
The pinned leanVM computes exactly this function, taking both flags as words:
`crates/flock/src/hash.rs:189-229` (`g_fn`, `initial_state`, `blake2s_compress`) at
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`. The RFC's Boolean `f` is the word `0xFFFFFFFF`.

**The cell encoding** is transcribed from `crates/leanvm_core/src/hash_flock.rs:110-132` and
`:155-178` (`words_of`, `pack_words`, `metadata`, `unpack_metadata`, `compression`, `digest`)
and `crates/leanvm_core/src/cpu/execute.rs:872-902` at the pin, and agrees with specification §2
(`doc/leanvm/body/02-vm-specification.tex:92-95`) and §7 (`07-instruction-tables.tex:114-123`):

* a canonical cell `a0 + a1·y` is the little-endian 128-bit value `a0 ‖ a1`, read as four 32-bit
  words, low word of `a0` first (`cellWords`);
* the sixteen message words are the four message cells in operand order, the eight
  chaining-value words are the two chaining-value cells, first cell first, and the eight output
  words fill the two output cells the same way;
* the metadata cell is `counter ‖ final ‖ last_node`: the 64-bit counter is limb 0, the two
  flag words are the low and high halves of limb 1 (`unpackMetadata`);
* all nine cells are canonical. The Rust executor checks the seven cells it reads and constructs
  the two outputs canonical; the constraints force all nine (§7: the eighteen low limbs are the
  values committed to Flock), and `CompressCells` follows the constraints.

### Deviation from the roadmap

`docs/roadmap/leanisa-blueprint.md` (Layer 1) types the two flags as `Bool`. The pinned Rust and
the Flock relation take them as the two 32-bit halves of limb 1 of the metadata cell, XORed into
`v[14]` and `v[15]` whatever their value, and a metadata cell with a flag word other than `0` or
`0xFFFFFFFF` satisfies the constraints. `compress` and `unpackMetadata` therefore carry `UInt32`
flags, so that `CompressCells` says what the constraints check on every metadata cell; the
Boolean form is `compress h m t (if f0 then 0xFFFFFFFF else 0) (if f1 then 0xFFFFFFFF else 0)`.
-/


/-! ### Compression -/

namespace Blake2s

/-- Rotate a 32-bit word right by `n` bits (RFC 7693 §2.3, `>>>`). -/
def rotr (x : UInt32) (n : ℕ) : UInt32 := ⟨x.toBitVec.rotateRight n⟩

/-- The mixing function `G` (RFC 7693 §3.1) with the BLAKE2s rotations `(16, 12, 8, 7)` (§2.1). -/
def mix (v : Vector UInt32 16) (a b c d : Fin 16) (x y : UInt32) : Vector UInt32 16 :=
  let va := v[a] + v[b] + x
  let vd := rotr (v[d] ^^^ va) 16
  let vc := v[c] + vd
  let vb := rotr (v[b] ^^^ vc) 12
  let va := va + vb + y
  let vd := rotr (vd ^^^ va) 8
  let vc := vc + vd
  let vb := rotr (vb ^^^ vc) 7
  (((v.set a va).set b vb).set c vc).set d vd

/-- One round of `F` (RFC 7693 §3.2): the four column and the four diagonal `G` calls, with the
message words selected by the schedule row `s`. -/
def round (v m : Vector UInt32 16) (s : Vector (Fin 16) 16) : Vector UInt32 16 :=
  let v := mix v 0 4 8 12 m[s[0]] m[s[1]]
  let v := mix v 1 5 9 13 m[s[2]] m[s[3]]
  let v := mix v 2 6 10 14 m[s[4]] m[s[5]]
  let v := mix v 3 7 11 15 m[s[6]] m[s[7]]
  let v := mix v 0 5 10 15 m[s[8]] m[s[9]]
  let v := mix v 1 6 11 12 m[s[10]] m[s[11]]
  let v := mix v 2 7 8 13 m[s[12]] m[s[13]]
  mix v 3 4 9 14 m[s[14]] m[s[15]]

/-- The initial working vector of `F`: `h`, then `iv` with the two counter words and the two
flag words XORed into its last four words (RFC 7693 §3.2; `blake2s-ref.c` for `v[15]`). -/
def initialState (h : Vector UInt32 8) (t : UInt64) (f0 f1 : UInt32) : Vector UInt32 16 :=
  let v : Vector UInt32 16 := h ++ iv
  let v := v.set 12 (v[12] ^^^ t.toUInt32)
  let v := v.set 13 (v[13] ^^^ (t >>> 32).toUInt32)
  let v := v.set 14 (v[14] ^^^ f0)
  v.set 15 (v[15] ^^^ f1)

end Blake2s

/-- The BLAKE2s compression function `F` (RFC 7693 §3.2) with the tree-mode last-node flag:
`t` is the 64-bit offset counter, `f0` the last-block flag and `f1` the last-node flag, each
`0xFFFFFFFF` when set. Ten rounds under `sigma`, then `h[i] ^ v[i] ^ v[i + 8]`. -/
def compress (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Vector UInt32 8 :=
  let v := sigma.foldl (fun v s ↦ Blake2s.round v m s) (Blake2s.initialState h t f0 f1)
  #v[h[0] ^^^ v[0] ^^^ v[8], h[1] ^^^ v[1] ^^^ v[9], h[2] ^^^ v[2] ^^^ v[10],
     h[3] ^^^ v[3] ^^^ v[11], h[4] ^^^ v[4] ^^^ v[12], h[5] ^^^ v[5] ^^^ v[13],
     h[6] ^^^ v[6] ^^^ v[14], h[7] ^^^ v[7] ^^^ v[15]]

/-! ### Cells -/

/-- The low 32 bits of a `K` element. -/
def lowWord (a : K) : UInt32 := ⟨a.toBitVec.extractLsb' 0 32⟩

/-- The high 32 bits of a `K` element. -/
def highWord (a : K) : UInt32 := ⟨a.toBitVec.extractLsb' 32 32⟩

/-- The `K` element with the given low and high words. -/
def ofWords (lo hi : UInt32) : K := BF64.ofBitVec (hi.toBitVec ++ lo.toBitVec)

/-- The four little-endian words of a canonical cell `a0 + a1·y`: the low and high words of `a0`,
then those of `a1` (`hash_flock.rs:110-114`, `words_of`; the top limb is ignored). -/
def cellWords (x : E) : Vector UInt32 4 :=
  #v[lowWord (x.limb 0), highWord (x.limb 0), lowWord (x.limb 1), highWord (x.limb 1)]

/-- The canonical cell holding four little-endian words (`hash_flock.rs:116-119`,
`pack_words`). -/
def wordsCell (w : Vector UInt32 4) : E :=
  E.ofLimbs (ofWords w[0] w[1]) (ofWords w[2] w[3]) 0

/-- The metadata cell `counter ‖ final ‖ last_node` (`hash_flock.rs:121-132`; specification §2):
the counter is limb 0, the last-block and last-node flag words are the low and high halves of
limb 1. -/
def unpackMetadata (md : E) : UInt64 × UInt32 × UInt32 :=
  (⟨(md.limb 0).toBitVec⟩, lowWord (md.limb 1), highWord (md.limb 1))

/-- The sixteen message words of the four message cells, in operand order
(`hash_flock.rs:155-165`). -/
def messageWords (m : Fin 4 → E) : Vector UInt32 16 :=
  cellWords (m 0) ++ cellWords (m 1) ++ cellWords (m 2) ++ cellWords (m 3)

/-- The `BLAKE2S` relation on its nine cells (specification §2 and
`07-instruction-tables.tex:114-123`): every cell is canonical, and
the two output cells hold the compression of the four message cells under the two chaining-value
cells and the metadata cell. -/
def CompressCells (m : Fin 4 → E) (cv0 cv1 out0 out1 md : E) : Prop :=
  (∀ i, IsCanonical128 (m i)) ∧ IsCanonical128 cv0 ∧ IsCanonical128 cv1 ∧
    IsCanonical128 out0 ∧ IsCanonical128 out1 ∧ IsCanonical128 md ∧
    cellWords out0 ++ cellWords out1 =
      compress (cellWords cv0 ++ cellWords cv1) (messageWords m) (unpackMetadata md).1
        (unpackMetadata md).2.1 (unpackMetadata md).2.2

/-- `CompressCells` is decided by comparing the output *lists* of words: core's `DecidableEq` for
`Vector` is not exposed to module-system importers, so neither `decide` nor the kernel can reduce
it there, while `List` equality reduces. -/
instance {m : Fin 4 → E} {cv0 cv1 out0 out1 md : E} :
    Decidable (CompressCells m cv0 cv1 out0 out1 md) :=
  decidable_of_iff
    ((∀ i, IsCanonical128 (m i)) ∧ IsCanonical128 cv0 ∧ IsCanonical128 cv1 ∧
      IsCanonical128 out0 ∧ IsCanonical128 out1 ∧ IsCanonical128 md ∧
      (cellWords out0 ++ cellWords out1).toList =
        (compress (cellWords cv0 ++ cellWords cv1) (messageWords m) (unpackMetadata md).1
          (unpackMetadata md).2.1 (unpackMetadata md).2.2).toList)
    (by simp only [CompressCells, Vector.toList_inj])

/-!
## One step of the machine

Category A: written from specification §2
(`doc/leanvm/body/02-vm-specification.tex`; the registers `:18-22`, the execution loop
`:28-37`, the operands `:51-54`, the instruction table `:56-70`, `DEREF` `:73-83`, `JUMP`
`:88`, `BLAKE2S` `:92-95`) before the Rust executor (`crates/leanvm_core/src/cpu/execute.rs`) was
opened; the diff against the executor is recorded in `docs/roadmap/leanisa-status.md`. Where §2
is silent the roadmap's pinned conventions decide: `DEREF` reads its local cell in every mode
(specification §7.4, acceptance test 6), and the halting test that keeps the sentinel from ever
being executed belongs to the loop, `LeanerVM.Semantics.Execution` (acceptance test 5).

**The registers** are two `K` elements, `pc` and `fp`, the pair `Regs K`; the structure is
parametric in the field so that the bus of Layer 5 carries the same pair over `Expression K`.
Every instruction but a taken `JUMP` advances to the fall-through successor
`Regs.next r = (g · pc, fp)`, the next bytecode slot in the same frame (§2, execution loop
step 2).

**One step** is `step prog L r = prog.fetch r.pc >>= execute L r`: fetch the instruction at
`pc` (`Program.fetch`), then `execute` it against the committed image `L`: read the cells it
names (`MemImage.read`, an operand `o` naming `fp · o`), check the instruction's relation on
the values read, and return the next registers. A failed fetch, a failed read, or a false
relation is `none`. Values are only ever read and compared: the image is fixed before
execution, so "`[o_C] = [o_A] + [o_B]`" is a check on three words, and a constraint row of
Layer 6 corresponds to a step by unfolding `execute` and `executeWith`. The arms are written
once, in `executeWith` over a named reader; `execute L r` is `executeWith L.read r`, and the
computable carrier of `LeanerVM.Semantics.Executable` is the same arms at a computable reader.

The arms of `executeWith`, in the order of §2's table:

* `XOR`, `MUL_NATIVE`: `[o_C] = [o_A] + [o_B]`, respectively `[o_A] · [o_B]`, in `E`.
* `SET_CONSTANT`: `[o] = k`.
* `DEREF`: the pointer `p = [o₁]` lies in `K`, and the cell `mem[p · o₂]` holds the source
  `derefSource mode`: the local cell `[o₃]`, the return address `g² · pc`, or `fp`.
* `JUMP`: `c = [o_c]`, `d = [o_d]`, `f = [o_f]` all lie in `K`, taken or not; the successor is
  `(d, f)` when `c ≠ 0` and `Regs.next` otherwise.
* `BLAKE2S`: the nine cells `[o_{m_i}]`, `[o_cv]`, `[g · o_cv]`, `[o_out]`, `[g · o_out]`,
  `[o_md]` satisfy `CompressCells` (`LeanerVM.Semantics.Blake2s`).

### Wrong readings excluded

* The successor of `pc` is `g · pc`, never `pc + 1` (acceptance test 3): `1 + 1 = 0` in `K`.
* `DEREF` reads three cells in every mode; the local cell `[o₃]` must be in range even when
  the mode ignores its value (acceptance test 6).
* `JUMP`'s three membership assertions are unconditional: `c = 0` with `d ∉ K` is `none`
  (acceptance test 7).
* All nine `BLAKE2S` cells are canonical, the two output cells included, through
  `CompressCells` (acceptance test 12).
* There is no second semantics. The six arms exist once, in `executeWith`; the carrier only
  changes the reader. The executor's write-once bookkeeping, back-solving, hints, and
  deferrals are witness generation, specified later against `step` (acceptance test 19).
-/


/-! ### Registers -/

/-- The two registers (specification §2), over a field `F`: `Regs K` is the machine's register
pair, and `Regs (Expression K)` a table row's, so that one structure serves the semantics and
the state channel of the bus (roadmap Layer 5). -/
structure Regs (F : Type) where
  /-- The program counter: the address of the instruction to execute. -/
  pc : F
  /-- The frame pointer: the base of the current frame, an operand `o` naming `fp · o`. -/
  fp : F
  deriving Repr

/-- Register equality is decided field by field. Not derived: the derived instance decides the
second field under `h ▸` for the first, whose `Eq.rec` makes the kernel compare two register
values by definitional unfolding instead of evaluation, and `g * 1 = g ^ 1` then never
decides (status finding E5). -/
instance {F : Type} [DecidableEq F] : DecidableEq (Regs F) := fun x y ↦
  decidable_of_iff (x.pc = y.pc ∧ x.fp = y.fp) (by cases x; cases y; simp)

/-- The fall-through successor `(g · pc, fp)`: the next bytecode slot, same frame (§2,
execution loop step 2). -/
def Regs.next (r : Regs K) : Regs K := ⟨g * r.pc, r.fp⟩

/-! ### `DEREF` -/

/-- The value a `DEREF` stores, by mode: the local cell `[o₃]`, the return address `g² · pc`,
or the frame pointer `fp`, the registers embedded in `E` (§2, `src(mode)`). -/
def derefSource : DerefMode → Regs K → E → E
  | .cell, _, v3 => v3
  | .pc, r, _ => ofK (g ^ 2 * r.pc)
  | .fp, r, _ => ofK r.fp

/-! ### The step -/

/-- The six arms of one instruction over a named reader `read`: read the cells the instruction
names, check its relation, and return the next registers; `none` on a failed read or a false
relation (§2, execution loop step 2, "execute inst"). The machine's step is `execute`, this
function at the image's reader `L.read`; the computable carrier (`LeanerVM.Semantics.Executable`)
instantiates the same arms with its own reader, so the arms exist once (acceptance test 19). -/
def executeWith (read : K → Option E) (r : Regs K) : Instr → Option (Regs K)
  | .xor oA oB oC => do
    let vA ← read (r.fp * oA)
    let vB ← read (r.fp * oB)
    let vC ← read (r.fp * oC)
    guard (vC = vA + vB)
    pure r.next
  | .mulNative oA oB oC => do
    let vA ← read (r.fp * oA)
    let vB ← read (r.fp * oB)
    let vC ← read (r.fp * oC)
    guard (vC = vA * vB)
    pure r.next
  | .setConstant o k => do
    let v ← read (r.fp * o)
    guard (v = k)
    pure r.next
  | .deref o1 o2 o3 mode => do
    let p ← read (r.fp * o1)
    guard (IsInK p)
    let v3 ← read (r.fp * o3)
    let v2 ← read (p.limb 0 * o2)
    guard (v2 = derefSource mode r v3)
    pure r.next
  | .jump oc od of => do
    let c ← read (r.fp * oc)
    let d ← read (r.fp * od)
    let f ← read (r.fp * of)
    guard (IsInK c ∧ IsInK d ∧ IsInK f)
    pure (if c = 0 then r.next else ⟨d.limb 0, f.limb 0⟩)
  | .blake2s om ocv oout omd => do
    let m0 ← read (r.fp * om 0)
    let m1 ← read (r.fp * om 1)
    let m2 ← read (r.fp * om 2)
    let m3 ← read (r.fp * om 3)
    let cv0 ← read (r.fp * ocv)
    let cv1 ← read (r.fp * (g * ocv))
    let out0 ← read (r.fp * oout)
    let out1 ← read (r.fp * (g * oout))
    let md ← read (r.fp * omd)
    guard (CompressCells ![m0, m1, m2, m3] cv0 cv1 out0 out1 md)
    pure r.next

/-- Execute one instruction from registers `r` over the committed image `L`: the arms of
`executeWith` at the image's reader `MemImage.read`, which is what makes the specification
noncomputable (§2, execution loop step 2). -/
noncomputable def execute {κ : ℕ} (L : MemImage κ) (r : Regs K) : Instr → Option (Regs K) :=
  executeWith L.read r

/-- One step of the machine: fetch the instruction at `pc` and execute it (§2, execution loop
steps 1–2); `none` when the counter fetches nothing. -/
noncomputable def step {κ : ℕ} (prog : Program) (L : MemImage κ) (r : Regs K) :
    Option (Regs K) :=
  prog.fetch r.pc >>= execute L r

/-!
## Valid executions

Category A: written from specification §2
(`doc/leanvm/body/02-vm-specification.tex`; the initial registers `:18-22`, the public input
`:26`, the execution loop `:28-37`, nondeterminism `:45-49`) and the boundary tuples of §6.1
(`06-bus-interactions.tex`), before the Rust executor was opened; the diff is recorded in
`docs/roadmap/leanisa-status.md`.

**The loop.** `run prog L n r` takes `n` steps from `r` over the image `L`, testing for the
sentinel before each fetch: a state whose counter is `Program.finalPc prog = g^(N_prog - 1)`,
the last bytecode slot, halts the machine, and stepping from it is `none`. So
`run prog L n Regs.initial = some (Regs.final prog)` says exactly that the machine starts at
`(1, 1)`, executes `n` instructions none of which sits in the sentinel slot, and arrives at
`(g^(N_prog - 1), 1)`: the halting test precedes the fetch (roadmap acceptance test 5; §2
places it after the execute step, status finding S1) and the final frame pointer is `1` (§6.1,
the boundary pull `(g^(N_prog - 1), g^0)`; acceptance test 4, finding S2).

**Traces and valid executions.** A `Trace prog` is what the prover chooses: the memory
log-size `κ`, the committed image, and the step count; all nondeterminism is the image (§2,
"Non determinism"). `HasPublicBoundary input t` is the verifier's boundary: `κ` within the caps
`16 ≤ κ ≤ 32`, and the two public words at `g^0` and `g^1`. `ValidExecution prog input t` is
the boundary together with the run. `Trace.regs` is the register sequence
`r_0 = (1, 1), r_1, …, r_steps` the state bus of Layer 8 embeds.

`ValidExecution` is a specification, not a program: `Program.fetch` and `MemImage.read` are
noncomputable, so a concrete execution is a proof that peels `run` one step at a time
(`run_succ_of_ne`), fetches and reads through `Program.fetch_gpow` and `MemImage.read_gpow`,
and decides each instruction's relation on literal words in the kernel.

### Wrong readings excluded

* The final frame pointer is required: a run reaching the sentinel with `fp ≠ 1` is not a
  `ValidExecution` (acceptance test 4).
* The sentinel is never executed: `run` is `none` from a state at `finalPc` for any positive
  step count (zero steps return that state), so a valid execution first arrives at the sentinel
  (`run_intermediate`), and the program with `N_prog = 1` has the empty execution
  (acceptance test 5).
* The boundary words sit at `g^0` and `g^1`, two lanes each (acceptance test 17).
-/


/-! ### Boundary registers -/

/-- The initial registers `(1, 1)`, that is `(g^0, g^0)` (specification §2). -/
def Regs.initial : Regs K := ⟨1, 1⟩

/-- The sentinel counter `g^(N_prog - 1)`, the last bytecode slot: reaching it halts the
machine, and it is never executed (§2, execution loop step 3; acceptance test 5). -/
def Program.finalPc (prog : Program) : K := gpow (2 ^ prog.logSize - 1)

/-- The sentinel is not a `JUMP`. This is a program-shape premise for constraint
soundness, not a condition on ISA validity or a promise that padding is possible.
The exact verifier-bound guest must establish it separately. It is the `sentinelSafe` field of
the roadmap's `WellFormedBytecode` (Layer 10), which refers to this definition rather than
restating it (acceptance test 20). -/
def SentinelSafe (prog : Program) : Prop :=
  (prog.code ⟨2 ^ prog.logSize - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩).opcode ≠ .jump

/-- Sentinel safety is checked from the last typed instruction, without an address search. -/
instance (prog : Program) : Decidable (SentinelSafe prog) :=
  inferInstanceAs (Decidable (_ ≠ Opcode.jump))

/-- The final registers `(g^(N_prog - 1), 1)`: the sentinel counter with the frame pointer back
at `1` (§6.1, the boundary pull; acceptance test 4). -/
def Regs.final (prog : Program) : Regs K := ⟨prog.finalPc, 1⟩

/-! ### The loop -/

/-- `n` steps from `r`, halting before each fetch: `some` the registers after `n` steps when
none of the `n` states stepped from is at the sentinel, `none` otherwise (§2, execution loop). -/
noncomputable def run {κ : ℕ} (prog : Program) (L : MemImage κ) : ℕ → Regs K → Option (Regs K)
  | 0, r => some r
  | n + 1, r => if r.pc = prog.finalPc then none else step prog L r >>= run prog L n

/-! ### Traces and valid executions -/

/-- What the prover chooses for a run of `prog`: the memory log-size, the committed image, and
the number of steps (§2, "Non determinism"). -/
structure Trace (prog : Program) where
  /-- The memory log-size `κ_mem`. -/
  κ : ℕ
  /-- The committed memory image. -/
  image : MemImage κ
  /-- The number of steps of the run. -/
  steps : ℕ

/-- The verifier's boundary on a trace: `16 ≤ κ ≤ 32`, and the two public words at `g^0` and
`g^1` (§2; §6.1). -/
def HasPublicBoundary {prog : Program} (input : PublicInput) (t : Trace prog) : Prop :=
  minLogMem ≤ t.κ ∧ t.κ ≤ maxLogMem ∧
    t.image.read (gpow 0) = some input.word0 ∧ t.image.read (gpow 1) = some input.word1

/-- A valid execution of `prog` on `input`: the boundary holds and `t.steps` steps from `(1, 1)`
halt at `(g^(N_prog - 1), 1)` (§2). -/
def ValidExecution (prog : Program) (input : PublicInput) (t : Trace prog) : Prop :=
  HasPublicBoundary input t ∧ run prog t.image t.steps Regs.initial = some (Regs.final prog)

end
end LeanerVM.Semantics
