import LeanerVM.Protocol.Verifier.Load

/-!
# `leanvm-verify`: the deployed verifier on the Python CLI's four files

`lake exe leanvm-verify <bytecode> <public input> <stream> <openings>` runs
`LeanerVM.Protocol.Verifier.verifyFiles`, the Lean transcription of `python-verifier/verifier.py`
at leanVM `127510d14c98ade4e8a97646c44fa7f1ff5e752d`, compiled, and prints the verdict in the
Python CLI's words; the exit code is `0` on acceptance. It imports the production verifier only.
-/

open LeanerVM.Protocol.Verifier

/-- The driver. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [bytecode, publicInput, stream, openings] =>
    let read := fun (p : String) => do return (← IO.FS.readBinFile p).toList
    if verifyFiles (← read bytecode) (← read publicInput) (← read stream) (← read openings) then
      IO.println "verification succeeded"
      return 0
    else
      IO.println "verification failed"
      return 1
  | _ =>
    IO.eprintln "usage: leanvm-verify <bytecode> <public input> <stream> <openings>"
    return 2
