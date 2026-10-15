"""Mutations of the Rust prover's proofs, and the pinned Python verifier's verdict on each.

The fixtures under tests/fixtures/verifier/ are proofs of the pinned leanVM Rust prover in the
Python verifier's four-file format (scripts/export-verifier-fixtures-rust.sh). This driver runs
the pinned `python-verifier/verifier.py` (leanVM a386121f84292f6fa663aaa3e570c15bc0240ea2) on
every fixture and on single-point mutations of it, and writes the cases with the Python's
verdicts to tests/fixtures/verifier/cases.txt, which
tests/LeanerVMTests/Protocol/Verifier/RustProofs.lean replays through the Lean `verify`,
requiring the same verdict on every line.

The mutation positions come from an instrumented run of the Python on the honest proof: the
stream offset where every phase of `verify_execution` starts, the root halves, every
proof-of-work nonce, and the byte offset and shape of every Merkle opening. Each case changes
one thing:

  flip <file> <offset>    XOR 0x01 into one byte (the low byte of a scalar's limb, a leaf word,
                          a sibling digest, a public input or bytecode byte);
  truncate <file> <n>     drop the last n bytes;
  append <file> <n>       append n zero bytes;
  none                    the honest proof.

Usage (from the repository root, with a leanVM source tree at the pin):
  python3 -I scripts/verifier-fixtures.py <leanVM source tree> tests/fixtures/verifier
  python3 -I scripts/verifier-fixtures.py <leanVM source tree> tests/fixtures/verifier --check --lean

`--check` reruns the Python on every case of the existing cases.txt and fails on a verdict that
differs from the recorded one, instead of rewriting the file. `--lean` then builds and runs
`lake exe verifier-diff` (tests/VerifierDiff.lean), the compiled Lean verifier on every case,
which fails on a verdict that differs from the Python's.
"""

import argparse
import hashlib
import importlib.util
import subprocess
import sys
import tempfile
from pathlib import Path

PIN = "a386121f84292f6fa663aaa3e570c15bc0240ea2"
VERIFIER_SHA256 = "28018d8c63cc9399d5751630ca59bf06d3c833b673949fe38102f65a04d83634"
FILES = ("bytecode.bin", "public_input.bin", "stream.bin", "merkle_openings.bin")
PHASES = ("sizes", "bus", "tables", "public", "flock", "ring", "whir")


def load_verifier(tree: Path):
    """A fresh copy of the pinned verifier module, so that instrumenting it touches no other."""
    path = tree / "python-verifier" / "verifier.py"
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != VERIFIER_SHA256:
        sys.exit(f"{path} is not the verifier at {PIN} (sha256 {digest})")
    spec = importlib.util.spec_from_file_location("pinned_verifier", path)
    module = importlib.util.module_from_spec(spec)
    sys.modules["pinned_verifier"] = module
    spec.loader.exec_module(module)
    return module


def instrument(V, directory: Path) -> dict:
    """Run the Python on the honest proof, recording where each phase and each opening starts."""
    events = {"phase": [], "nonce": [], "root": [], "merkle": []}
    state = {"transcript": None}
    original_init = V.Transcript.__init__

    def init(self, *args, **kwargs):
        original_init(self, *args, **kwargs)
        state["transcript"] = self

    def offset() -> int:
        return state["transcript"].stream_offset

    def phase(name, function):
        def wrapped(*args, **kwargs):
            events["phase"].append((name, offset()))
            return function(*args, **kwargs)

        return wrapped

    original_grind = V.Transcript.grind_check

    def grind(self, bits):
        events["nonce"].append(self.stream_offset)
        return original_grind(self, bits)

    original_merkle = V.Transcript.merkle

    def merkle(self, root, block_length, queries, leaf_words):
        start = self.opening_offset
        result = original_merkle(self, root, block_length, queries, leaf_words)
        events["merkle"].append((start, len(queries), V.log2_strict(block_length), leaf_words))
        return result

    original_from_halves = V.Digest.from_halves.__func__

    def from_halves(cls, low, high):
        events["root"].append(offset() - 2)
        return original_from_halves(cls, low, high)

    V.Transcript.__init__ = init
    V.Transcript.grind_check = grind
    V.Transcript.merkle = merkle
    V.Digest.from_halves = classmethod(from_halves)
    for name, attribute in (("bus", "verify_bus_balance"), ("flock", "verify_flock"), ("ring", "ring_switch"),
                            ("whir", "verify_stacked_opening")):
        setattr(V, attribute, phase(name, getattr(V, attribute)))
    original_table = V.table_sumcheck

    # The public input phase starts where the table sumcheck ends.
    def table(*args, **kwargs):
        result = original_table(*args, **kwargs)
        events["phase"].append(("public", offset()))
        return result

    V.table_sumcheck = phase("tables", table)
    events["phase"].append(("sizes", 0))
    code = V.main([str(directory / name) for name in FILES])
    assert code == 0, "the honest proof is rejected"
    transcript = state["transcript"]
    events["stream_length"] = len(transcript.proof.stream)
    events["openings_length"] = len(transcript.proof.merkle_openings)
    return events


def cases_for(name: str, events: dict) -> list[tuple[str, ...]]:
    cases = [(name, "none")]
    starts = dict(events["phase"])
    bounds = [starts[p] for p in PHASES] + [events["stream_length"]]
    for index, phase in enumerate(PHASES):
        first, end = bounds[index], bounds[index + 1]
        if first == end:  # ring switching reads no scalar
            continue
        for position in sorted({first, (first + end) // 2, end - 1}):
            for limb in (0, 2):
                cases.append((name, "flip", "stream.bin", str(24 * position + 8 * limb), f"{phase} scalar {position} limb {limb}"))
    for position in events["root"]:
        cases.append((name, "flip", "stream.bin", str(24 * position), f"root half at scalar {position}"))
    for position in events["nonce"]:
        cases.append((name, "flip", "stream.bin", str(24 * position), f"nonce at scalar {position}"))
    for level, (start, count, height, words) in enumerate(events["merkle"]):
        size = 8 * words + 32 * height
        last = start + (count - 1) * size
        cases.append((name, "flip", "merkle_openings.bin", str(start), f"level {level} first leaf, word 0"))
        cases.append((name, "flip", "merkle_openings.bin", str(last + 8 * words - 8), f"level {level} last leaf, last word"))
        cases.append((name, "flip", "merkle_openings.bin", str(start + 8 * words), f"level {level} first sibling"))
        cases.append((name, "flip", "merkle_openings.bin", str(last + size - 1), f"level {level} last opening, top sibling"))
    cases.append((name, "flip", "public_input.bin", "0", "public input byte 0"))
    cases.append((name, "flip", "public_input.bin", "31", "public input byte 31"))
    cases.append((name, "flip", "bytecode.bin", "0", "bytecode word 0"))
    cases.append((name, "truncate", "stream.bin", "24", "last scalar dropped"))
    cases.append((name, "append", "stream.bin", "24", "zero scalar appended"))
    cases.append((name, "truncate", "stream.bin", "1", "stream cut mid-scalar"))
    cases.append((name, "truncate", "merkle_openings.bin", "32", "last sibling dropped"))
    cases.append((name, "append", "merkle_openings.bin", "8", "word appended to the openings"))
    return cases


def apply(source: Path, target: Path, case: tuple[str, ...]) -> None:
    for name in FILES:
        (target / name).write_bytes((source / name).read_bytes())
    if case[1] == "none":
        return
    operation, file, argument = case[1], case[2], int(case[3])
    data = bytearray((target / file).read_bytes())
    if operation == "flip":
        data[argument] ^= 0x01
    elif operation == "truncate":
        del data[len(data) - argument :]
    elif operation == "append":
        data.extend(bytes(argument))
    (target / file).write_bytes(bytes(data))


def python_verdict(tree: Path, directory: Path) -> tuple[str, str]:
    run = subprocess.run(
        [sys.executable, "-I", str(tree / "python-verifier" / "verifier.py"), *(str(directory / name) for name in FILES)],
        capture_output=True, text=True,
    )
    message = (run.stdout + run.stderr).strip().splitlines()[-1]
    return ("accept" if run.returncode == 0 and message == "verification succeeded" else "reject"), message


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("tree", type=Path)
    parser.add_argument("fixtures", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--lean", action="store_true", help="then run the compiled Lean verifier on every case")
    arguments = parser.parse_args()
    tree, fixtures = arguments.tree.resolve(), arguments.fixtures.resolve()
    cases_path = fixtures / "cases.txt"
    if arguments.check:
        cases = []
        for line in cases_path.read_text().splitlines():
            if line and not line.startswith("#"):
                fields, _, note = line.partition(" # ")
                *case, verdict = fields.split()
                cases.append((tuple(case), verdict, note))
    else:
        load_verifier(tree)
        cases = []
        for directory in sorted(p for p in fixtures.iterdir() if p.is_dir()):
            events = instrument(load_verifier(tree), directory)
            print(f"{directory.name}: phases {events['phase']}, nonces {events['nonce']}, "
                  f"roots {events['root']}, openings {[e[:2] for e in events['merkle']]}", file=sys.stderr)
            cases += [(c[:4] if c[1] != "none" else c[:2], None, c[4] if len(c) > 4 else "honest") for c in cases_for(directory.name, events)]
    lines = [f"# Cases of tests/LeanerVMTests/Protocol/Verifier/RustProofs.lean: fixture, mutation, the verdict of",
             f"# python-verifier/verifier.py at leanVM {PIN}, and its message. Written by",
             "# scripts/verifier-fixtures.py; do not edit."]
    failures = 0
    with tempfile.TemporaryDirectory() as scratch:
        scratch = Path(scratch)
        for case, recorded, note in cases:
            apply(fixtures / case[0], scratch, case)
            verdict, message = python_verdict(tree, scratch)
            if recorded is not None and verdict != recorded:
                failures += 1
                print(f"MISMATCH {' '.join(case)}: recorded {recorded}, Python {verdict} ({message})", file=sys.stderr)
            label = note.split(" | ")[0]
            lines.append(f"{' '.join(case)} {verdict} # {label} | {message}")
            print(lines[-1], file=sys.stderr)
    if not arguments.check:
        cases_path.write_text("\n".join(lines) + "\n")
    if arguments.lean:
        root = Path(__file__).resolve().parent.parent
        subprocess.run(["lake", "build", "verifier-diff"], cwd=root, check=True)
        lean = subprocess.run(["lake", "exe", "verifier-diff", str(fixtures)], cwd=root)
        failures += lean.returncode != 0
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
