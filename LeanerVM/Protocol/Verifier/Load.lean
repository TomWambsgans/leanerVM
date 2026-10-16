/-
  LeanerVM.Protocol.Verifier.Load

  The byte files the Python verifier reads, decoded into the inputs of `verify`: the bytecode,
  the public input, the scalar stream, and the Merkle openings cut into the shapes the verifier
  opens them at. Each decoder is the inverse of a serializer.
-/

module

public import LeanerVM.Protocol.Verifier.Verify
import LeanerVM.Protocol.Compile.Rom.Encoding

/-!
# Loading a proof from the Python verifier's files

Category B: transcribed from `python-verifier/verifier.py` at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2`, lines 104-106 (`E.from_bytes`), 204-224 (`Digest`),
322-332 (`Proof.load`), 385-401 (`Transcript._merkle_data`, `Transcript.merkle`) and 1417-1434
(`main`). The pinned Rust prover writes the same files
(`crates/lean_vm/tests/verifiers/python_verifier.rs`, `python_verify`).

The four files:

* `bytecode.bin`: the bytecode table, 8 little-endian bytes per `K` word (`decodeWords`);
* `public_input.bin`: the 32 bytes of the public input digest (`decodeDigest`);
* `stream.bin`: the scalar stream, 24 bytes per `E` element, its three limbs in order
  (`decodeScalars`);
* `merkle_openings.bin`: every Merkle opening in the order the verifier reads them, each its
  leaf's words (8 bytes each) and then one 32-byte sibling per level, with no length fields.

## Cutting the openings

The Python reads the openings file lazily, `8 · leaf_words` bytes then `32 · height` bytes per
queried position, the shape coming from the commitment it opens. `Proof.openings` is that byte
string already cut (`LeanerVM.Protocol.Compile.Run`, *Deviation*). The cut is computed here from
the verifier's own configuration rather than by a second interpreter of the program: the
announced sizes at the head of the stream, read by the program's own `readSizes`, fix the stack's
log-size and the rate exponent, and `deriveConfig` fixes the WHIR ladder, whose level `ℓ` opens
commitment `ℓ` at `queries_ℓ` positions in the shape `levelShape` gives (`openingShapes`). These
are the only openings the program makes (commitment `0` is the stack, read by `commitStack`; the
others are WHIR's), and `sampleQueries` returns exactly `queries_ℓ` positions.

The cut is sound with no appeal to that argument: `openOne` checks every opening's width and
height against the commitment it is opened against, and `runProof` requires every opening to be
consumed, so `verify` accepts a cut only if it is the one the program reads; and then its bytes
are the Python's reads in order (`encodeOpenings_splitOpenings`). It is complete by the
round-trip `splitOpenings_encodeOpenings`, given that the shapes are the program's, which the
differential test on the Rust prover's proofs exercises.

## Round trips

Every decoder inverts a serializer, both ways: decoding a serialized value gives it back, and a
byte string that decodes is the serialization of what it decodes to.
-/

namespace LeanerVM.Protocol.Verifier

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol.Compile
open LeanerVM.Protocol.Blake2sHash LeanerVM.Protocol.Compile.Rom

@[expose] public section

/-! ## Words -/

/-- The word of four little-endian bytes. -/
def wordOfBytes (b0 b1 b2 b3 : UInt8) : UInt32 :=
  UInt32.ofNat (b0.toNat + 2 ^ 8 * b1.toNat + 2 ^ 16 * b2.toNat + 2 ^ 24 * b3.toNat)

/-- Read `n` values of `size` bytes each with `decode`, and the bytes after them; `none` if the
bytes run out (checked on the next `size` bytes, not on the length of all the rest). -/
def readMany {α : Type} (size : ℕ) (decode : Bytes → α) : ℕ → Bytes → Option (List α × Bytes)
  | 0, b => some ([], b)
  | n + 1, b =>
    if (b.take size).length = size then
      (readMany size decode n (b.drop size)).map fun r ↦ (decode (b.take size) :: r.1, r.2)
    else none

/-- The `K` word of eight little-endian bytes (`int.from_bytes(…, "little")`). -/
def kOfBytes (b : Bytes) : K :=
  ofWords (wordOfBytes (b.getD 0 0) (b.getD 1 0) (b.getD 2 0) (b.getD 3 0))
    (wordOfBytes (b.getD 4 0) (b.getD 5 0) (b.getD 6 0) (b.getD 7 0))

/-- The digest of 32 bytes, its words little-endian (`Digest`). -/
def digestOfBytes (b : Bytes) : Digest :=
  Vector.ofFn fun j : Fin 8 ↦
    wordOfBytes (b.getD (4 * j) 0) (b.getD (4 * j + 1) 0) (b.getD (4 * j + 2) 0)
      (b.getD (4 * j + 3) 0)

/-- The scalar of 24 bytes, three little-endian limbs (`E.from_bytes`). -/
def eOfBytes (b : Bytes) : E := E.ofLimbs (kOfBytes b) (kOfBytes (b.drop 8)) (kOfBytes (b.drop 16))

/-- The 24 bytes of a scalar (`E.to_bytes`). -/
def eBytes (x : E) : Bytes := kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2)

/-! ## The files -/

/-- Read exactly the whole of a byte string as values of `size` bytes. -/
def decodeAll {α : Type} (size : ℕ) (decode : Bytes → α) (b : Bytes) : Option (List α) :=
  match readMany size decode (b.length / size) b with
  | some (xs, []) => some xs
  | _ => none

/-- `bytecode.bin`: the bytecode's words (`main`, `verifier.py:1428-1429`). -/
def decodeWords (b : Bytes) : Option (List K) := decodeAll 8 kOfBytes b

/-- `public_input.bin`: the 32-byte public input (`Digest.__post_init__`). -/
def decodeDigest (b : Bytes) : Option Digest :=
  if b.length = 32 then some (digestOfBytes b) else none

/-- `stream.bin`: the scalars (`Proof.load`). -/
def decodeScalars (b : Bytes) : Option (List E) := decodeAll 24 eOfBytes b

/-- The stream's bytes. -/
def encodeScalars (xs : List E) : Bytes := xs.flatMap eBytes

/-- An opening's bytes: its leaf's words, then its siblings from the leaf up
(`Transcript.merkle`). -/
def openingBytes (o : Opening) : Bytes := o.leaf.flatMap kBytes ++ o.path.flatMap digestBytes

/-- The openings file's bytes. -/
def encodeOpenings (os : List Opening) : Bytes := os.flatMap openingBytes

/-- Read one opening of the given height and width (`Transcript._merkle_data`). -/
def readOpening (height width : ℕ) (b : Bytes) : Option (Opening × Bytes) := do
  let (leaf, b) ← readMany 8 kOfBytes width b
  let (path, b) ← readMany 32 digestOfBytes height b
  return (⟨leaf, path⟩, b)

/-- Read one opening per shape `(height, width)`, in order. -/
def readOpenings : List (ℕ × ℕ) → Bytes → Option (List Opening × Bytes)
  | [], b => some ([], b)
  | (height, width) :: shapes, b => do
    let (o, b) ← readOpening height width b
    let (os, b) ← readOpenings shapes b
    return (o :: os, b)

/-- Cut the openings file into openings of the given shapes, consuming it. -/
def splitOpenings (shapes : List (ℕ × ℕ)) (b : Bytes) : Option (List Opening) :=
  match readOpenings shapes b with
  | some (os, []) => some os
  | _ => none

/-! ## The shapes the verifier opens -/

/-- The openings of WHIR's levels after the first, the message log before each level's folds
given: `queries` positions of the next commitment's shape (`levelShape`). -/
def laterOpeningShapes : ℕ → List Whir.Level → List (ℕ × ℕ)
  | _, [] => []
  | messageLog, level :: rest =>
    List.replicate level.queries (levelShape messageLog level (3 * 2 ^ level.fold)) ++
      laterOpeningShapes (messageLog - level.fold) rest

/-- The openings of a WHIR run on a `logN`-variable stack, level by level: level `0` opens the
stack at `commitStack`'s shape, level `ℓ + 1` the commitment read at level `ℓ`
(`verify_whir`, `verifier.py:1006-1087`). -/
def whirOpeningShapes (logN : ℕ) : List Whir.Level → List (ℕ × ℕ)
  | [] => []
  | level :: rest =>
    List.replicate level.queries (levelShape logN level (2 ^ level.fold)) ++
      laterOpeningShapes (logN - level.fold) rest

/-- The announced layout and rate exponent of a stream, read by the program's own `readSizes`
(the hash is not consulted for a value: reads only absorb). -/
def announced (bytecode : List K) (stream : List E) : Option (Layout × ℕ) :=
  (Id.run (Compile.run (fun _ ↦ pure default) (readSizes bytecode) ⟨default, stream, [], []⟩)).map
    (·.1)

/-- The shape of every opening `verify` makes on a proof with this stream, in order. -/
def openingShapes (bytecode : List K) (stream : List E) : Option (List (ℕ × ℕ)) := do
  let (layout, logInverseRate) ← announced bytecode stream
  let config ← deriveConfig layout.stackLog logInverseRate
  return whirOpeningShapes layout.stackLog config

/-- The proof in the files `stream.bin` and `merkle_openings.bin`, for this bytecode. -/
def loadProof (bytecode : List K) (stream openings : Bytes) : Option Proof := do
  let scalars ← decodeScalars stream
  let shapes ← openingShapes bytecode scalars
  let openings ← splitOpenings shapes openings
  return ⟨scalars, openings⟩

/-- **The verifier on the four files**: decode them and run `verify`; a file that does not
decode is rejected, as the Python rejects it. -/
def verifyFiles (bytecode publicInput stream openings : Bytes) : Bool :=
  match decodeWords bytecode, decodeDigest publicInput with
  | some words, some digest =>
    match loadProof words stream openings with
    | some π => verify words digest π
    | none => false
  | _, _ => false

/-! ## Round trips -/

/-- A word is read back from its four bytes (`wordBytes`). -/
theorem wordOfBytes_wordBytes (w : UInt32) :
    wordOfBytes w.toUInt8 (w >>> 8).toUInt8 (w >>> 16).toUInt8 (w >>> 24).toUInt8 = w := by
  apply UInt32.toNat_inj.mp
  simp only [wordOfBytes, UInt32.toNat_ofNat, UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]
  have := w.toNat_lt
  norm_num at this ⊢
  omega

theorem wordBytes_wordOfBytes (b0 b1 b2 b3 : UInt8) :
    wordBytes (wordOfBytes b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  have h2 := b2.toNat_lt
  have h3 := b3.toNat_lt
  simp only [wordBytes, wordOfBytes, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;>
    simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt32.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] <;> norm_num at h0 h1 h2 h3 ⊢ <;> omega

/-- A `K` word is read back from the head of its bytes. -/
theorem kOfBytes_kBytes_append (a : K) (rest : Bytes) : kOfBytes (kBytes a ++ rest) = a := by
  have hl := wordOfBytes_wordBytes (lowWord a)
  have hh := wordOfBytes_wordBytes (highWord a)
  simpa [kOfBytes, kBytes, wordBytes, hl, hh] using ofWords_lowWord_highWord a

theorem kOfBytes_kBytes (a : K) : kOfBytes (kBytes a) = a := by
  simpa using kOfBytes_kBytes_append a []

/-- The bytes of the word read from the head of a byte string are its first eight. -/
theorem kBytes_kOfBytes {b : Bytes} (h : 8 ≤ b.length) : kBytes (kOfBytes b) = b.take 8 := by
  match b, h with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest, _ =>
    simp [kOfBytes, kBytes, lowWord_ofWords, highWord_ofWords, wordBytes_wordOfBytes]

theorem digestOfBytes_digestBytes (d : Digest) : digestOfBytes (digestBytes d) = d := by
  obtain ⟨⟨l⟩, hl⟩ := d
  match l, hl with
  | [w0, w1, w2, w3, w4, w5, w6, w7], _ =>
    have := wordOfBytes_wordBytes
    ext j hj
    interval_cases j <;> simp [digestOfBytes, digestBytes, wordBytes, this]

theorem digestBytes_digestOfBytes {b : Bytes} (h : b.length = 32) :
    digestBytes (digestOfBytes b) = b := by
  match b, h with
  | [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
      b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31], _ =>
    simp [digestOfBytes, digestBytes, wordBytes_wordOfBytes, Vector.toList_ofFn, List.ofFn_succ]

theorem eBytes_length (x : E) : (eBytes x).length = 24 := rfl

theorem eOfBytes_eBytes (x : E) : eOfBytes (eBytes x) = x := by
  simp only [eOfBytes, eBytes, List.append_assoc, kOfBytes_kBytes_append]
  rw [show 16 = 8 + 8 from rfl, ← List.drop_drop, List.drop_left' (kBytes_length _),
    List.drop_left' (kBytes_length _), kOfBytes_kBytes_append, kOfBytes_kBytes]
  exact ofLimbs_limb x

theorem eBytes_eOfBytes {b : Bytes} (h : b.length = 24) : eBytes (eOfBytes b) = b := by
  simp only [eBytes, eOfBytes, limb_ofLimbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [kBytes_kOfBytes (by omega), kBytes_kOfBytes (by simp; omega),
    kBytes_kOfBytes (by simp; omega), List.take_of_length_le (l := b.drop 16) (by simp; omega),
    show 16 = 8 + 8 from rfl, ← List.drop_drop, List.append_assoc, List.take_append_drop,
    List.take_append_drop]


/-! ### Lists of fixed-size values -/

section ReadMany

variable {α : Type} {size : ℕ} {decode : Bytes → α} {enc : α → Bytes}

theorem length_flatMap_of_length (hlen : ∀ x, (enc x).length = size) (xs : List α) :
    (xs.flatMap enc).length = xs.length * size := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, hlen, ih, Nat.succ_mul, Nat.add_comm]

/-- Reading values back from their bytes gives them, and the bytes after them. -/
theorem readMany_flatMap (hlen : ∀ x, (enc x).length = size) (hdec : ∀ x, decode (enc x) = x)
    (xs : List α) (rest : Bytes) :
    readMany size decode xs.length (xs.flatMap enc ++ rest) = some (xs, rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readMany,
      List.take_left' (hlen x), hlen x, ↓reduceIte, List.drop_left' (hlen x), ih, hdec,
      Option.map_some]

/-- What is read is the head of the bytes: the values' bytes, then the rest. -/
theorem readMany_spec (henc : ∀ c, c.length = size → enc (decode c) = c) :
    ∀ {n : ℕ} {b rest : Bytes} {xs : List α}, readMany size decode n b = some (xs, rest) →
      xs.length = n ∧ xs.flatMap enc ++ rest = b
  | 0, b, rest, xs, h => by
    simp only [readMany, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | n + 1, b, rest, xs, h => by
    simp only [readMany] at h
    split_ifs at h with hs
    obtain ⟨⟨ys, r⟩, hr, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨h1, h2⟩ := readMany_spec henc hr
    refine ⟨by simp [h1], ?_⟩
    rw [List.flatMap_cons, henc _ hs, List.append_assoc, h2, List.take_append_drop]

theorem decodeAll_flatMap (hpos : 0 < size) (hlen : ∀ x, (enc x).length = size)
    (hdec : ∀ x, decode (enc x) = x) (xs : List α) :
    decodeAll size decode (xs.flatMap enc) = some xs := by
  have h := readMany_flatMap hlen hdec xs []
  rw [List.append_nil] at h
  simp only [decodeAll, length_flatMap_of_length hlen, Nat.mul_div_cancel _ hpos, h]

theorem decodeAll_spec (henc : ∀ c, c.length = size → enc (decode c) = c) {b : Bytes}
    {xs : List α} (h : decodeAll size decode b = some xs) : xs.flatMap enc = b := by
  unfold decodeAll at h
  split at h
  · rename_i hr
    cases h
    simpa using (readMany_spec henc hr).2
  · cases h

end ReadMany

/-! ### The files -/

theorem kBytes_kOfBytes_of_length {c : Bytes} (h : c.length = 8) : kBytes (kOfBytes c) = c := by
  rw [kBytes_kOfBytes (by omega), List.take_of_length_le (by omega)]

theorem digestBytes_length' (d : Digest) : (digestBytes d).length = 32 := digestBytes_length d

/-- **The bytecode file round-trips**: a word list is read back from its bytes. -/
theorem decodeWords_flatMap (ws : List K) : decodeWords (ws.flatMap kBytes) = some ws :=
  decodeAll_flatMap (by decide) kBytes_length kOfBytes_kBytes ws

/-- A bytecode file that decodes is the bytes of its words. -/
theorem flatMap_of_decodeWords {b : Bytes} {ws : List K} (h : decodeWords b = some ws) :
    ws.flatMap kBytes = b :=
  decodeAll_spec (fun _ ↦ kBytes_kOfBytes_of_length) h

/-- **The stream file round-trips**: a stream is read back from its bytes. -/
theorem decodeScalars_encodeScalars (xs : List E) : decodeScalars (encodeScalars xs) = some xs :=
  decodeAll_flatMap (by decide) eBytes_length eOfBytes_eBytes xs

/-- A stream file that decodes is the bytes of its scalars. -/
theorem encodeScalars_of_decodeScalars {b : Bytes} {xs : List E} (h : decodeScalars b = some xs) :
    encodeScalars xs = b :=
  decodeAll_spec (fun _ ↦ eBytes_eOfBytes) h

/-- **The public input file round-trips.** -/
theorem decodeDigest_digestBytes (d : Digest) : decodeDigest (digestBytes d) = some d := by
  simp [decodeDigest, digestBytes_length, digestOfBytes_digestBytes]

/-- A public input file that decodes is the bytes of its digest. -/
theorem digestBytes_of_decodeDigest {b : Bytes} {d : Digest} (h : decodeDigest b = some d) :
    digestBytes d = b := by
  unfold decodeDigest at h
  split_ifs at h with hl
  cases h
  exact digestBytes_digestOfBytes hl

/-! ### The openings -/

/-- An opening's shape: its height (siblings) and width (leaf words). -/
def openingShape (o : Opening) : ℕ × ℕ := (o.path.length, o.leaf.length)

theorem readOpening_bytes (o : Opening) (rest : Bytes) :
    readOpening o.path.length o.leaf.length (openingBytes o ++ rest) = some (o, rest) := by
  simp [readOpening, openingBytes, readMany_flatMap kBytes_length kOfBytes_kBytes,
    readMany_flatMap digestBytes_length digestOfBytes_digestBytes]

theorem readOpening_spec {height width : ℕ} {b rest : Bytes} {o : Opening}
    (h : readOpening height width b = some (o, rest)) :
    openingShape o = (height, width) ∧ openingBytes o ++ rest = b := by
  simp only [readOpening, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨leaf, b1⟩, h1, ⟨path, b2⟩, h2, he⟩ := h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  obtain ⟨hl1, hb1⟩ := readMany_spec (fun _ ↦ kBytes_kOfBytes_of_length) h1
  obtain ⟨hl2, hb2⟩ := readMany_spec (fun _ ↦ digestBytes_digestOfBytes) h2
  refine ⟨by simp [openingShape, hl1, hl2], ?_⟩
  simp only [openingBytes, List.append_assoc, hb2, hb1]

theorem readOpenings_encodeOpenings (os : List Opening) (rest : Bytes) :
    readOpenings (os.map openingShape) (encodeOpenings os ++ rest) = some (os, rest) := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    simp only [List.map_cons, openingShape, encodeOpenings, List.flatMap_cons,
      List.append_assoc, readOpenings, readOpening_bytes]
    simp only [encodeOpenings] at ih
    simp [ih]

theorem readOpenings_spec :
    ∀ {shapes : List (ℕ × ℕ)} {b rest : Bytes} {os : List Opening},
      readOpenings shapes b = some (os, rest) →
        os.map openingShape = shapes ∧ encodeOpenings os ++ rest = b
  | [], b, rest, os, h => by
    simp only [readOpenings, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [encodeOpenings]
  | (height, width) :: shapes, b, rest, os, h => by
    simp only [readOpenings, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨o, b1⟩, h1, ⟨os', b2⟩, h2, he⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hs1, hb1⟩ := readOpening_spec h1
    obtain ⟨hs2, hb2⟩ := readOpenings_spec h2
    refine ⟨by simp [hs1, hs2], ?_⟩
    simp only [encodeOpenings, List.flatMap_cons, List.append_assoc] at hb2 ⊢
    rw [hb2, hb1]

/-- **The openings file round-trips**: openings are cut back out of their bytes at their own
shapes. -/
theorem splitOpenings_encodeOpenings (os : List Opening) :
    splitOpenings (os.map openingShape) (encodeOpenings os) = some os := by
  have h := readOpenings_encodeOpenings os []
  rw [List.append_nil] at h
  simp only [splitOpenings, h]

/-- An openings file that is cut is the bytes of its openings, in the shapes asked for. -/
theorem encodeOpenings_splitOpenings {shapes : List (ℕ × ℕ)} {b : Bytes} {os : List Opening}
    (h : splitOpenings shapes b = some os) :
    os.map openingShape = shapes ∧ encodeOpenings os = b := by
  unfold splitOpenings at h
  split at h
  · rename_i hr
    cases h
    simpa using readOpenings_spec hr
  · cases h

end
end LeanerVM.Protocol.Verifier
