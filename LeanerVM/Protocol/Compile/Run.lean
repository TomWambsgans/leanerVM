/-
  LeanerVM.Protocol.Compile.Run

  The compiled reading of a verifier program: the deployed non-interactive verifier, run on a
  proof with a hash function in any monad, its challenges squeezed out of the BLAKE2s
  Fiat–Shamir chain and its rows authenticated by Merkle paths.
-/

module

public import LeanerVM.Protocol.Compile.Prog
public import LeanerVM.Protocol.Blake2sHash

/-!
# The compiled verifier

Category B, transcribed from the Python verifier at leanVM
`a386121f84292f6fa663aaa3e570c15bc0240ea2` (`python-verifier/verifier.py:322-417`, `Proof`,
`compress`, `Transcript`), whose Fiat–Shamir chain is the Rust's
(`crates/fiat_shamir/src/lib.rs:18-174`):

* the chain state is a 256-bit digest `cv`; every step is BLAKE2s-256 of the 64 bytes
  `cv ‖ block`, a block being three little-endian 64-bit words of data and a 64-bit tag
  (`blockOf`): `1` to absorb a scalar, `2` to squeeze, `3` for the proof-of-work base, `4` for a
  nonce;
* `read`: `cv ← H(cv ‖ (x, 1))` for the next scalar `x` of the stream (`next_scalar`);
* `sample`: `cv ← H(cv ‖ (0, 2))`, the challenge being the three low 64-bit words of the new
  state (`sample`, `challengeOf`);
* `grind`: the next scalar of the stream is the nonce `n`, *not* absorbed by `observe`; the
  check is that the low `bits` bits of the first word of `H(H(cv ‖ (0, 3)) ‖ (n, 4))` are zero
  (for `bits = 0`, that `n = 0`); then `cv ← H(cv ‖ (n, 4))` (`grind_check`);
* `commit`: the root is read as two scalars, both absorbed, and must be canonical
  (`Digest.from_halves`, `digestOfScalars`);
* `query`: one opening per position, in order, from a separate channel that the chain does not
  absorb: the leaf's words, hashed as bytes, then one sibling per level, the position's bit at
  the level choosing the side, and the climb must end at the root (`Transcript.merkle`). The
  leaf must have the committed width and the path the committed height; the Python checks both
  implicitly by reading exactly that many bytes, and `Proof` here carries the openings already
  split.

The hash is a parameter `H : Bytes → m Digest` in any monad `m`: the deployed verifier is the
`Id` instance at `blake2sBytes`, and the random-oracle theorem runs the same function with `H`
a query to the oracle.

## Deviation from the Python verifier

The Python verifier reads the Merkle openings from one byte string; `Proof.openings` is that
string already cut into leaves and paths. A byte string that does not cut into the lengths the
verifier asks for is rejected by the Python, and has no `Proof` here; nothing else differs.
-/

namespace LeanerVM.Protocol.Compile

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol.Blake2sHash

@[expose] public section

/-- Byte strings, the hash's inputs. -/
abbrev Bytes : Type := List UInt8

/-- Digests are finite: the uniform distribution of the random oracle ranges over them. A proof
object only: its element list has `2^256` entries, and compiled code would build it when the
program starts (a closed constant is evaluated at initialization), so it is `noncomputable`. -/
noncomputable instance instFintypeDigest : Fintype Digest :=
  Fintype.ofEquiv (Fin 8 → UInt32)
    { toFun := Vector.ofFn, invFun := fun v i ↦ v[i]
      left_inv := fun _ ↦ funext fun _ ↦ Vector.getElem_ofFn _
      right_inv := fun _ ↦ Vector.ext fun _ _ ↦ Vector.getElem_ofFn _ }

/-! ## The chain's blocks -/

/-- The eight little-endian bytes of a 64-bit tag. -/
def tagBytes (tag : ℕ) : Bytes := [tag.toUInt8, 0, 0, 0, 0, 0, 0, 0]

/-- The 32-byte block of a scalar and a tag: its three limbs, then the tag (`lib.rs:36-43`). -/
def blockOf (x : E) (tag : ℕ) : Bytes :=
  kBytes (x.limb 0) ++ kBytes (x.limb 1) ++ kBytes (x.limb 2) ++ tagBytes tag

/-- The challenge squeezed into a state: its three low 64-bit words (`verifier.py:356-358`). -/
def challengeOf (d : Digest) : E :=
  E.ofLimbs (ofWords d[0] d[1]) (ofWords d[2] d[3]) (ofWords d[4] d[5])

/-- The proof-of-work predicate: at `bits = 0` the nonce is `0`; otherwise the low `bits` bits
of the digest's first 64-bit word are zero (`verifier.py:377-383`). -/
def powOk (bits : ℕ) (nonce : E) (d : Digest) : Bool :=
  if bits = 0 then decide (nonce.limb 0 = 0 ∧ nonce.limb 1 = 0 ∧ nonce.limb 2 = 0)
  else decide ((d[0].toNat + 2 ^ 32 * d[1].toNat) % 2 ^ bits = 0)

/-! ## Proofs and verifier states -/

/-- One Merkle opening: the leaf's words and the siblings from the leaf up. -/
structure Opening where
  /-- The leaf's words. -/
  leaf : List K
  /-- The siblings, from the leaf's level up. -/
  path : List Digest

/-- A proof: the scalar stream and the Merkle openings, in the order the verifier reads them
(`verifier.py:322-332`). -/
structure Proof where
  /-- The scalars. -/
  stream : List E
  /-- The openings. -/
  openings : List Opening

/-- The compiled verifier's state: the chain state, what is left of the proof, and the roots
read so far with their shapes. -/
structure St where
  /-- The chain state. -/
  cv : Digest
  /-- The scalars not yet read. -/
  stream : List E
  /-- The openings not yet read. -/
  openings : List Opening
  /-- The roots read so far, each with its height and width. -/
  roots : List (Digest × ℕ × ℕ)

/-! ## The run -/

section Run

variable {m : Type → Type} [Monad m] (H : Bytes → m Digest)

/-- The chain after absorbing a block. -/
def absorbBlock (cv : Digest) (block : Bytes) : m Digest := H (digestBytes cv ++ block)

/-- Climb a Merkle path from `node` at position `q`: at each level the position's low bit says
whether `node` is the left child (`verifier.py:396-397`). -/
def climb : Digest → ℕ → List Digest → m Digest
  | node, _, [] => pure node
  | node, q, s :: ss => do
    let parent ← if q % 2 = 0 then H (digestBytes node ++ digestBytes s)
      else H (digestBytes s ++ digestBytes node)
    climb parent (q / 2) ss

/-- Check one opening against a root of the given shape at position `q`. -/
def openOne (root : Digest) (height width q : ℕ) (o : Opening) : m Bool :=
  if o.leaf.length = width ∧ o.path.length = height then do
    let leafDigest ← H (o.leaf.flatMap kBytes)
    let top ← climb H leafDigest q o.path
    pure (decide (top.toList = root.toList))
  else pure false

/-- Open every position in order, consuming one opening each; the leaves, and the openings
left. -/
def openAll (root : Digest) (height width : ℕ) :
    List ℕ → List Opening → m (Option (List (List K) × List Opening))
  | [], os => pure (some ([], os))
  | _ :: _, [] => pure none
  | q :: qs, o :: os => do
    if ← openOne H root height width q o then
      let rest ← openAll root height width qs os
      pure (rest.map fun r ↦ (o.leaf :: r.1, r.2))
    else pure none

/-- The compiled reading of a program: run it on the state, every challenge squeezed out of the
chain and every opening authenticated; `none` on rejection. -/
def run {α : Type} : Prog α → St → m (Option (α × St))
  | .ret a, s => pure (some (a, s))
  | .fail, _ => pure none
  | .read k, s => match s.stream with
    | [] => pure none
    | x :: xs => do
      let cv ← absorbBlock H s.cv (blockOf x 1)
      run (k x) { s with cv := cv, stream := xs }
  | .sample k, s => do
    let cv ← absorbBlock H s.cv (blockOf 0 2)
    run (k (challengeOf cv)) { s with cv := cv }
  | .grind bits k, s => match s.stream with
    | [] => pure none
    | n :: xs => do
      let base ← absorbBlock H s.cv (blockOf 0 3)
      let d ← absorbBlock H base (blockOf n 4)
      let cv ← absorbBlock H s.cv (blockOf n 4)
      if powOk bits n d then run k { s with cv := cv, stream := xs } else pure none
  | .commit height width k, s => match s.stream with
    | x0 :: x1 :: xs => do
      let cv0 ← absorbBlock H s.cv (blockOf x0 1)
      let cv1 ← absorbBlock H cv0 (blockOf x1 1)
      match digestOfScalars (x0, x1) with
      | some root =>
        run k { s with cv := cv1, stream := xs, roots := s.roots ++ [(root, height, width)] }
      | none => pure none
    | _ => pure none
  | .query i ps k, s => match s.roots[i]? with
    | none => pure none
    | some (root, height, width) => do
      match ← openAll H root height width ps s.openings with
      | some (rows, rest) => run (k rows) { s with openings := rest }
      | none => pure none

/-- Run a program on a proof from a seed state, and accept when it returns `true` with the
stream and the openings fully consumed (`verifier.py:415-417`, `finish`). -/
def runProof (P : Prog Bool) (seed : Digest) (π : Proof) : m Bool := do
  match ← run H P ⟨seed, π.stream, π.openings, []⟩ with
  | some (true, s) => pure (s.stream.isEmpty && s.openings.isEmpty)
  | _ => pure false

end Run

end
end LeanerVM.Protocol.Compile
