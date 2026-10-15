import LeanerVMTests.Protocol.Verifier.RustProofs

/-!
# `verifier-diff`: the Lean verifier against the Python's verdicts, compiled

`lake exe verifier-diff <fixtures> [fixture …]` runs `verifyFiles` on every case of
`<fixtures>/cases.txt` (`tests/LeanerVMTests/Protocol/Verifier/RustProofs.lean`), one line per
case, and exits nonzero if any verdict differs from the pinned Python verifier's recorded one.
`lake exe verifier-diff --files <bytecode> <public input> <stream> <openings>` prints the
verdict on four files, in the Python CLI's words.
-/

open LeanerVMTests.Protocol.Verifier.RustProofs

/-- The driver. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--files", bytecode, publicInput, stream, openings] =>
    let f : Files := {
      bytecode := ← IO.FS.readBinFile bytecode
      publicInput := ← IO.FS.readBinFile publicInput
      stream := ← IO.FS.readBinFile stream
      openings := ← IO.FS.readBinFile openings }
    if f.verdict then
      IO.println "verification succeeded"
      return 0
    else
      IO.println "verification failed"
      return 1
  | root :: only =>
    let start ← IO.monoMsNow
    let mismatches ← checkCases root (if only.isEmpty then none else some only)
    IO.println s!"{mismatches} verdict(s) differ from the Python's; {(← IO.monoMsNow) - start} ms"
    return if mismatches = 0 then 0 else 1
  | [] =>
    IO.eprintln "usage: verifier-diff <fixtures> [fixture …]"
    IO.eprintln "       verifier-diff --files <bytecode> <public input> <stream> <openings>"
    return 2
