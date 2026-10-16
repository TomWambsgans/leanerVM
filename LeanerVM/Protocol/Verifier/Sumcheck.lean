/-
  LeanerVM.Protocol.Verifier.Sumcheck

  The sumcheck rounds of leanVM's Python verifier as programs of the verifier language: a round
  polynomial read with one coefficient derived from the claim, in its two modes, and a run of
  rounds.
-/

module

public import LeanerVM.Protocol.Compile.Prog
public import LeanerVM.Protocol.Verifier.Arith

/-!
# Sumcheck rounds

Category B: transcribed from `python-verifier/verifier.py` at leanVM
`127510d14c98ade4e8a97646c44fa7f1ff5e752d`, lines 405-412 (`Transcript.sumcheck_round_poly`) and
419-426 (`sumcheck`).

A round polynomial `q(X) = c0 + c1·X + c2·X² + …` of `count` coefficients is sent with one
coefficient left out, which the verifier derives from the running claim:

* plain mode (`eq_factor = None`), `q(0) + q(1) = claim`: the prover sends `c0`, then
  `c2, …, c_{count-1}`; `c1 = claim + Σ_{k ≥ 2} c_k` (characteristic two);
* equality mode (`eq_factor = r`), `(1 + r)·q(0) + r·q(1) = claim`: the prover sends
  `c1, …, c_{count-1}`; `c0 = claim + r·Σ_{k ≥ 1} c_k`.

Every coefficient sent is read (`Prog.read`, the Python's `next_scalar`), so absorbed into the
Fiat–Shamir chain in that order. The round's challenge is sampled after its polynomial, and the
next claim is `q(challenge)`.
-/

namespace LeanerVM.Protocol.Verifier

open LeanerVM.Parameters LeanerVM.Protocol.Compile

@[expose] public section

/-- Fail on `none`: a pure step the Python performs with a `require` inside. -/
def liftOption {α : Type} : Option α → Prog α
  | none => Prog.fail
  | some a => Prog.ret a

/-- `Transcript.sumcheck_round_poly(count, claim, eq_factor)`: read a round polynomial of `count`
coefficients, deriving the one the claim fixes; its coefficients, constant first
(`verifier.py:405-412`). -/
def sumcheckRoundPoly (count : ℕ) (claim : E) : Option E → Prog (List E)
  | none => do
    let constant ← Prog.readE
    let tail ← Prog.readN (count - 2)
    return constant :: (claim + sumE tail) :: tail
  | some eqFactor => do
    let tail ← Prog.readN (count - 1)
    return (claim + eqFactor * sumE tail) :: tail

/-- `sumcheck(transcript, claim, count, equalities)`: one round per entry of `equalities`, each
reading its polynomial and sampling its challenge; the challenges in order, and the final claim
(`verifier.py:419-426`). -/
def sumcheck (claim : E) (count : ℕ) : List (Option E) → Prog (List E × E)
  | [] => return ([], claim)
  | equality :: equalities => do
    let message ← sumcheckRoundPoly count claim equality
    let challenge ← Prog.sampleE
    let (point, final) ← sumcheck (polyEval message challenge) count equalities
    return (challenge :: point, final)

end
end LeanerVM.Protocol.Verifier
