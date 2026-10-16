/-
  LeanerVM.Semantics

  leanISA, the instruction set of leanVM: memory, instructions, programs, one step of the
  machine, and valid executions.
-/

module

public import LeanerVM.Parameters.Generator
public import LeanerVM.Parameters.Isa
public import LeanerVM.Parameters.Blake2s
public import LeanerVM.Parameters.Field

/-!
# leanISA

The leanVM instruction set, from §2 of the leanVM specification at
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`.

Words are elements of `E = K[y]/(y³ + y + 1)`, `K = GF(2^64)`. Addresses are powers of the
generator `g` of `K*`: memory word `i` and bytecode slot `i` both sit at `g^i`. The machine has two
registers, `pc` and `fp`. The memory is fixed before the run and only read: every instruction
checks a relation on the words it reads, so all nondeterminism is the choice of the memory.
-/

namespace LeanerVM.Semantics

open LeanerVM.Parameters

@[expose] public section

/-! ## Memory -/

open Classical in
/-- The index of an address: `some i` when `a = g^i` with `i < 2^κ`, otherwise `none`. -/
noncomputable def gLog? (κ : ℕ) (a : K) : Option (Fin (2 ^ κ)) :=
  if h : ∃ i : Fin (2 ^ κ), a = gpow i then some (Classical.choose h) else none

/-- A memory of `2^κ` words, by index. -/
abbrev MemImage (κ : ℕ) : Type := Fin (2 ^ κ) → E

/-- The word at address `a`, if `a` is an address. -/
noncomputable def MemImage.read {κ : ℕ} (L : MemImage κ) (a : K) : Option E :=
  (gLog? κ a).map L

/-- The public input: 256 bits, as four `K` lanes. -/
structure PublicInput where
  /-- The four lanes. -/
  lanes : Fin 4 → K
  deriving DecidableEq

/-- Memory word `0` holds `lane₀ + lane₁·y`. -/
def PublicInput.word0 (p : PublicInput) : E := E.ofLimbs (p.lanes 0) (p.lanes 1) 0

/-- Memory word `1` holds `lane₂ + lane₃·y`. -/
def PublicInput.word1 (p : PublicInput) : E := E.ofLimbs (p.lanes 2) (p.lanes 3) 0

/-! ## Instructions and programs

An operand `o` names the word at `fp · o`, written `[o]`. -/

/-- What a `DEREF` stores: a local word, the return address, or the frame pointer. -/
inductive DerefMode
  | cell
  | pc
  | fp
  deriving DecidableEq, Repr

/-- The six instructions. -/
inductive Instr
  /-- `[o_C] = [o_A] + [o_B]`. -/
  | xor (oA oB oC : K)
  /-- `[o_C] = [o_A] · [o_B]`. -/
  | mulNative (oA oB oC : K)
  /-- `[o] = k`. -/
  | setConstant (o : K) (k : E)
  /-- The word at address `[o₁] · o₂` is the source `mode` selects (`derefSource`). -/
  | deref (o1 o2 o3 : K) (mode : DerefMode)
  /-- Jump to `([o_d], [o_f])` if `[o_c] ≠ 0`. -/
  | jump (oc od of : K)
  /-- `([o_out], [g·o_out])` is the BLAKE2s compression of the message `[o_m₀], …, [o_m₃]` under
  the chaining value `([o_cv], [g·o_cv])`, with counter and flags `[o_md]`. -/
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

/-- A program: `2^logSize` instructions, instruction `i` at address `g^i`. -/
structure Program where
  /-- The log of the number of instructions. -/
  logSize : ℕ
  /-- At most `2^32` instructions. -/
  logSize_le : logSize ≤ maxLogBytecode
  /-- The instructions. -/
  code : Fin (2 ^ logSize) → Instr

/-- The instruction at address `pc`. -/
noncomputable def Program.fetch (prog : Program) (pc : K) : Option Instr :=
  (gLog? prog.logSize pc).map prog.code

/-! ## BLAKE2s

The compression function of RFC 7693 with the last-node flag of the BLAKE2 paper, as leanVM
computes it; and how its 32-bit words are stored in memory words. -/

namespace Blake2s

/-- Rotate right by `n` bits. -/
def rotr (x : UInt32) (n : ℕ) : UInt32 := ⟨x.toBitVec.rotateRight n⟩

/-- The mixing function `G`. -/
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

/-- One round: four column and four diagonal mixes, message words chosen by `s`. -/
def round (v m : Vector UInt32 16) (s : Vector (Fin 16) 16) : Vector UInt32 16 :=
  let v := mix v 0 4 8 12 m[s[0]] m[s[1]]
  let v := mix v 1 5 9 13 m[s[2]] m[s[3]]
  let v := mix v 2 6 10 14 m[s[4]] m[s[5]]
  let v := mix v 3 7 11 15 m[s[6]] m[s[7]]
  let v := mix v 0 5 10 15 m[s[8]] m[s[9]]
  let v := mix v 1 6 11 12 m[s[10]] m[s[11]]
  let v := mix v 2 7 8 13 m[s[12]] m[s[13]]
  mix v 3 4 9 14 m[s[14]] m[s[15]]

/-- The initial state: `h`, then `iv` with the counter and the two flag words XORed in. -/
def initialState (h : Vector UInt32 8) (t : UInt64) (f0 f1 : UInt32) : Vector UInt32 16 :=
  let v : Vector UInt32 16 := h ++ iv
  let v := v.set 12 (v[12] ^^^ t.toUInt32)
  let v := v.set 13 (v[13] ^^^ (t >>> 32).toUInt32)
  let v := v.set 14 (v[14] ^^^ f0)
  v.set 15 (v[15] ^^^ f1)

end Blake2s

/-- The compression of the message `m` under the chaining value `h`, with counter `t`, last-block
flag word `f0` and last-node flag word `f1`: ten rounds, then `h[i] ^ v[i] ^ v[i + 8]`. -/
def compress (h : Vector UInt32 8) (m : Vector UInt32 16) (t : UInt64) (f0 f1 : UInt32) :
    Vector UInt32 8 :=
  let v := sigma.foldl (fun v s ↦ Blake2s.round v m s) (Blake2s.initialState h t f0 f1)
  #v[h[0] ^^^ v[0] ^^^ v[8], h[1] ^^^ v[1] ^^^ v[9], h[2] ^^^ v[2] ^^^ v[10],
     h[3] ^^^ v[3] ^^^ v[11], h[4] ^^^ v[4] ^^^ v[12], h[5] ^^^ v[5] ^^^ v[13],
     h[6] ^^^ v[6] ^^^ v[14], h[7] ^^^ v[7] ^^^ v[15]]

/-- The low 32 bits of a `K` element. -/
def lowWord (a : K) : UInt32 := ⟨a.toBitVec.extractLsb' 0 32⟩

/-- The high 32 bits of a `K` element. -/
def highWord (a : K) : UInt32 := ⟨a.toBitVec.extractLsb' 32 32⟩

/-- The `K` element with these low and high 32 bits. -/
def ofWords (lo hi : UInt32) : K := BF64.ofBitVec (hi.toBitVec ++ lo.toBitVec)

/-- The four 32-bit words of a memory word `a₀ + a₁·y`, little-endian. -/
def cellWords (x : E) : Vector UInt32 4 :=
  #v[lowWord (x.limb 0), highWord (x.limb 0), lowWord (x.limb 1), highWord (x.limb 1)]

/-- The memory word holding four 32-bit words. -/
def wordsCell (w : Vector UInt32 4) : E :=
  E.ofLimbs (ofWords w[0] w[1]) (ofWords w[2] w[3]) 0

/-- The metadata word: the counter is limb 0, the two flag words are the halves of limb 1. -/
def unpackMetadata (md : E) : UInt64 × UInt32 × UInt32 :=
  (⟨(md.limb 0).toBitVec⟩, lowWord (md.limb 1), highWord (md.limb 1))

/-- The sixteen message words of four memory words. -/
def messageWords (m : Fin 4 → E) : Vector UInt32 16 :=
  cellWords (m 0) ++ cellWords (m 1) ++ cellWords (m 2) ++ cellWords (m 3)

/-- What `BLAKE2S` checks: the nine words have no `y²` term, and the output is the compression
of the message under the chaining value and the metadata. -/
def CompressCells (m : Fin 4 → E) (cv0 cv1 out0 out1 md : E) : Prop :=
  (∀ i, IsCanonical128 (m i)) ∧ IsCanonical128 cv0 ∧ IsCanonical128 cv1 ∧
    IsCanonical128 out0 ∧ IsCanonical128 out1 ∧ IsCanonical128 md ∧
    cellWords out0 ++ cellWords out1 =
      compress (cellWords cv0 ++ cellWords cv1) (messageWords m) (unpackMetadata md).1
        (unpackMetadata md).2.1 (unpackMetadata md).2.2

/-- `CompressCells` is decidable (compared as lists of words, which the kernel reduces). -/
instance {m : Fin 4 → E} {cv0 cv1 out0 out1 md : E} :
    Decidable (CompressCells m cv0 cv1 out0 out1 md) :=
  decidable_of_iff
    ((∀ i, IsCanonical128 (m i)) ∧ IsCanonical128 cv0 ∧ IsCanonical128 cv1 ∧
      IsCanonical128 out0 ∧ IsCanonical128 out1 ∧ IsCanonical128 md ∧
      (cellWords out0 ++ cellWords out1).toList =
        (compress (cellWords cv0 ++ cellWords cv1) (messageWords m) (unpackMetadata md).1
          (unpackMetadata md).2.1 (unpackMetadata md).2.2).toList)
    (by simp only [CompressCells, Vector.toList_inj])

/-! ## One step -/

/-- The registers: the program counter and the frame pointer. -/
structure Regs (F : Type) where
  /-- The program counter. -/
  pc : F
  /-- The frame pointer. -/
  fp : F
  deriving Repr

/-- The next instruction, same frame: `(g · pc, fp)`. -/
def Regs.next (r : Regs K) : Regs K := ⟨g * r.pc, r.fp⟩

/-- What a `DEREF` stores: the local word `[o₃]`, the return address `g² · pc`, or `fp`. -/
def derefSource : DerefMode → Regs K → E → E
  | .cell, _, v3 => v3
  | .pc, r, _ => ofK (g ^ 2 * r.pc)
  | .fp, r, _ => ofK r.fp

/-- Execute an instruction with the memory reader `read`: read its words, check its relation, and
return the next registers; `none` if a read or a check fails. -/
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

/-- Execute an instruction on the memory `L`. -/
noncomputable def execute {κ : ℕ} (L : MemImage κ) (r : Regs K) : Instr → Option (Regs K) :=
  executeWith L.read r

/-- One step: fetch the instruction at `pc` and execute it. -/
noncomputable def step {κ : ℕ} (prog : Program) (L : MemImage κ) (r : Regs K) :
    Option (Regs K) :=
  prog.fetch r.pc >>= execute L r

/-! ## Valid executions -/

/-- The machine starts at `(pc, fp) = (1, 1)`. -/
def Regs.initial : Regs K := ⟨1, 1⟩

/-- The last bytecode slot, `g^(2^logSize − 1)`: reaching it halts the machine. -/
def Program.finalPc (prog : Program) : K := gpow (2 ^ prog.logSize - 1)

/-- The machine halts at `(finalPc, 1)`. -/
def Regs.final (prog : Program) : Regs K := ⟨prog.finalPc, 1⟩

/-- `n` steps from `r`, halting at `finalPc`: `none` if a step fails or the machine halts first. -/
noncomputable def run {κ : ℕ} (prog : Program) (L : MemImage κ) : ℕ → Regs K → Option (Regs K)
  | 0, r => some r
  | n + 1, r => if r.pc = prog.finalPc then none else step prog L r >>= run prog L n

/-- An execution: a memory of `2^κ` words and a number of steps. -/
structure Trace (prog : Program) where
  /-- The log of the memory size. -/
  κ : ℕ
  /-- The memory. -/
  image : MemImage κ
  /-- The number of steps. -/
  steps : ℕ

/-- The memory has between `2^16` and `2^32` words and holds the public input in words `0`, `1`. -/
def HasPublicBoundary {prog : Program} (input : PublicInput) (t : Trace prog) : Prop :=
  minLogMem ≤ t.κ ∧ t.κ ≤ maxLogMem ∧
    t.image.read (gpow 0) = some input.word0 ∧ t.image.read (gpow 1) = some input.word1

/-- **A valid execution** of `prog` on `input`: the memory holds the public input, and `t.steps`
steps from `(1, 1)` halt at `(finalPc, 1)`. -/
def ValidExecution (prog : Program) (input : PublicInput) (t : Trace prog) : Prop :=
  HasPublicBoundary input t ∧ run prog t.image t.steps Regs.initial = some (Regs.final prog)

/-- The last instruction is not a `JUMP`: the one condition knowledge soundness puts on a
program. -/
def SentinelSafe (prog : Program) : Prop :=
  (prog.code ⟨2 ^ prog.logSize - 1, Nat.sub_lt (Nat.two_pow_pos _) (by decide)⟩).opcode ≠ .jump

end
end LeanerVM.Semantics
