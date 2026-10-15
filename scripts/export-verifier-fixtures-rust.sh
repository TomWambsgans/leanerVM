#!/usr/bin/env bash
# Prove small guest programs with the pinned leanVM Rust prover and write each proof in the
# format the pinned Python verifier reads (`python-verifier/verifier.py`, `Proof.load`, and
# `crates/lean_vm/tests/verifiers/python_verifier.rs` at a386121f84292f6fa663aaa3e570c15bc0240ea2):
#
#   bytecode.bin          the bytecode table, little-endian 64-bit words;
#   public_input.bin      the public input's two halves, 16 bytes each (c0, c1 little-endian);
#   stream.bin            the raw scalar stream, 24-byte little-endian E elements;
#   merkle_openings.bin   every opening in order: its leaf words, then its sibling digests.
#
# The proof is the RAW proof a Rust `verify` returns (`VerifySummary::raw`), each query carrying
# its full Merkle path, written exactly as `python_verify` in python_verifier.rs writes it. The
# guest is that test's program at a smaller loop count. Every proof is checked with the pinned
# Python verifier before the script returns. The fixtures are consumed by
# tests/LeanerVMTests/Protocol/Verifier/RustProofs.lean and scripts/verifier-fixtures.py.
#
# Usage: scripts/export-verifier-fixtures-rust.sh <leanVM source tree at the pin> <output dir>
#
# The source tree is a git checkout at the pin or an export of it
# (`git -C <leanVM> archive <pin> | tar -x -C <dir>`); either way the Python verifier's hash is
# checked against the pin's. Requires `cargo` and `python3`.
set -euo pipefail

pin="a386121f84292f6fa663aaa3e570c15bc0240ea2"
verifier_sha256="28018d8c63cc9399d5751630ca59bf06d3c833b673949fe38102f65a04d83634"
checkout="$(cd "${1:?usage: $0 <leanVM source tree> <output dir>}" && pwd)"
out="${2:?usage: $0 <leanVM source tree> <output dir>}"

if git -C "$checkout" rev-parse HEAD >/dev/null 2>&1 \
    && [[ "$(git -C "$checkout" rev-parse --show-toplevel)" == "$checkout" ]]; then
  head="$(git -C "$checkout" rev-parse HEAD)"
  if [[ "$head" != "$pin" ]]; then
    echo "leanVM checkout is at $head, not the pin $pin" >&2
    exit 1
  fi
fi
actual="$(sha256sum "$checkout/python-verifier/verifier.py" | cut -d' ' -f1)"
if [[ "$actual" != "$verifier_sha256" ]]; then
  echo "python-verifier/verifier.py is not the pin's (sha256 $actual)" >&2
  exit 1
fi

work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/src" "$out"
out="$(cd "$out" && pwd)"
cp "$checkout/Cargo.lock" "$work/Cargo.lock"
# The workspace's `target-cpu=native`, so that the prover runs its vectorized kernels.
mkdir -p "$work/.cargo"
cp "$checkout/.cargo/config.toml" "$work/.cargo/config.toml"

cat > "$work/Cargo.toml" <<EOF
[package]
name = "export-verifier-fixtures"
version = "0.0.0"
edition = "2024"

[dependencies]
lean_vm = { path = "$checkout/crates/lean_vm" }
lean_compiler = { path = "$checkout/crates/lean_compiler" }
fiat_shamir = { path = "$checkout/crates/fiat_shamir" }
primitives = { path = "$checkout/crates/primitives" }

[profile.release]
lto = "thin"
codegen-units = 1
EOF

cat > "$work/src/main.rs" <<'EOF'
use fiat_shamir::transcript::RawProof;
use lean_compiler::{compile, parse_with_replacements};
use lean_vm::cpu::{prove, verify};
use primitives::field::{F64, F192, g_pow};
use std::collections::BTreeMap;
use std::path::Path;

// The program of crates/lean_vm/tests/verifiers/python_verifier.rs, its loop count a parameter.
const SOURCE: &str = r#"
from snark_lib import *

LOOP_STEPS = LOOP_STEPS_PLACEHOLDER

def mix(value, tag):
    # A JUMP condition is K-valued (a g-power here), never an arbitrary word.
    if tag == 0:
        return value
    return value * GEN + value

def main():
    seed = [5, 7]
    digest = StackBuf(2)
    blake2s(seed, seed, digest)

    chain = HeapBuf(LOOP_STEPS + 1)
    chain[1] = digest[0]
    for index in mul_range(1, GEN ** LOOP_STEPS):
        chain[index * GEN] = mix(chain[index] + index, index) + index

    public = GEN ** 0
    public[1] = chain[GEN ** LOOP_STEPS]
    public[GEN] = mix(digest[1], GEN ** 0)
    return
"#;

// The public input the program computes (python_verifier.rs, `public_input`).
fn public_input(loop_steps: usize) -> [F192; 2] {
    use lean_vm::hash_flock::{FINAL_FLAG, IV, PINNED_T, compression, digest, metadata};

    let seed = [F64(5), F64::ZERO, F64(7), F64::ZERO];
    let metadata = metadata(PINNED_T, FINAL_FLAG, 0);
    let digest = digest(&compression(seed, seed, IV, metadata));
    let digest = [
        F192::new(digest[0].0, digest[1].0, 0),
        F192::new(digest[2].0, digest[3].0, 0),
    ];
    let mut value = digest[0];
    let mut index = F192::ONE;
    let generator = F192::from(g_pow(1));
    for _ in 0..loop_steps {
        let candidate = value + index;
        let product = candidate * generator;
        value = (if product == F192::ZERO {
            candidate
        } else {
            product + candidate
        }) + index;
        index *= generator;
    }
    [value, digest[1] * generator + digest[1]]
}

// python_verifier.rs, `python_verify`, the writing half.
fn write_raw(directory: &Path, raw: &RawProof) {
    let mut stream = Vec::new();
    for scalar in &raw.stream {
        for limb in [scalar.c0, scalar.c1, scalar.c2] {
            stream.extend(limb.to_le_bytes());
        }
    }
    let mut openings = Vec::new();
    for opening in &raw.merkle {
        for word in &opening.leaf_data {
            openings.extend(word.0.to_le_bytes());
        }
        for digest in &opening.path {
            openings.extend(digest);
        }
    }
    std::fs::write(directory.join("stream.bin"), stream).expect("write scalar stream");
    std::fs::write(directory.join("merkle_openings.bin"), openings).expect("write Merkle openings");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out = Path::new(&args[1]);
    for (loop_steps, log_inv_rate) in [(4usize, 1usize), (4, 4), (300, 2)] {
        let name = format!("chain{loop_steps}-rate{log_inv_rate}");
        let directory = out.join(&name);
        std::fs::create_dir_all(&directory).expect("create fixture directory");
        let replacements =
            BTreeMap::from([("LOOP_STEPS_PLACEHOLDER".to_string(), loop_steps.to_string())]);
        let ast = parse_with_replacements(SOURCE, &replacements).expect("parse zkDSL program");
        let program = compile(&ast);
        let public_input = public_input(loop_steps);
        let (proof, stats) = prove(&program, public_input, log_inv_rate);
        let raw = verify(&program, &public_input, &proof).expect("honest proof verifies").raw;
        let table: Vec<u8> = lean_vm::cpu::layout::bytecode_table(&program.prog)
            .iter()
            .flat_map(|w| w.0.to_le_bytes())
            .collect();
        std::fs::write(directory.join("bytecode.bin"), &table).expect("write bytecode");
        let pi: Vec<u8> = public_input
            .iter()
            .flat_map(|v| [v.c0.to_le_bytes(), v.c1.to_le_bytes()].concat())
            .collect();
        std::fs::write(directory.join("public_input.bin"), &pi).expect("write public input");
        write_raw(&directory, &raw);
        println!(
            "{name}: {} instructions, {} cycles, {} scalars, {} openings",
            program.prog.len(),
            stats.cycles,
            raw.stream.len(),
            raw.merkle.len(),
        );
    }
}
EOF

cargo run --quiet --release --manifest-path "$work/Cargo.toml" --target-dir "$checkout/target" \
  -- "$out"

for directory in "$out"/*/; do
  printf '%s: ' "$(basename "$directory")"
  python3 -I "$checkout/python-verifier/verifier.py" "$directory/bytecode.bin" \
    "$directory/public_input.bin" "$directory/stream.bin" "$directory/merkle_openings.bin"
done
