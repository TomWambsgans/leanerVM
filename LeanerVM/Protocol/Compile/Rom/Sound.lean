/-
  LeanerVM.Protocol.Compile.Rom.Sound

  The random-oracle theorem of the compiled verifier: Fiat–Shamir with proof of work and Merkle
  commitments (BCS) turns a doom certificate of a verifier program into a bound on the
  probability that the compiled verifier, run with BLAKE2s modelled as a random oracle, accepts
  a proof whose extracted history passes through doom.
-/

module

public import LeanerVM.Protocol.Compile.Rom.Step
public import LeanerVM.Protocol.Compile.Rom.Final
public import LeanerVM.Protocol.Compile.Rom.Bridge

/-!
# The random-oracle theorem of the compiled verifier

Let `P : Prog Bool` be a verifier program (`LeanerVM.Protocol.Compile.Prog`) with a doom
certificate `C : Cert P`, and `σ : Seed` the seeding of the Fiat–Shamir chain. The compiled
verifier (`verifierComp σ P`, `LeanerVM.Protocol.Compile.Run`) seeds the chain by `σ`, then
runs `P` on the proof, every hash a query to one random oracle `Bytes →ₒ Digest`.

In the experiment `romExperiment A (verifierComp σ P)` the adversary `A`, an oracle computation
with at most `Q_A` queries, outputs a proof `π`; the verifier, with at most `Q_V` queries on
every proof, runs on `π` against the same lazily sampled random oracle. `romSound` bounds the
probability that the verifier accepts while some boundary prefix of the *extracted history*
is doomed:

  `Pr[accept ∧ ∃ h₀ ≤ extractedHistory, Boundary h₀ ∧ C.D h₀]`
  `  ≤ (Q_A + Q_V) · (εmax + failBound σ (Q_A + Q_V))`,

where

* `εmax` bounds `2^-min(grindBits h, 64) · C.ε h` for every history `h`: the certificate's
  escape bound of each group of challenges, discounted by the proof of work before it;
* `failBound σ N = (4 + k) · N / 2^256`, `k` the number of seeding steps: the probability that a
  fresh answer collides with or predicts a digest the oracle's log already refers to;
* the extracted history (`extractedHistory`) is the interactive history of the verifier's run
  on `π`, every hash answered by the final random-oracle cache, every commitment holding the
  word extracted for its root from that cache (`extract`), `[]` if the run does not reach a
  verdict. Its doomed boundary prefixes are what the knowledge extractor reads off: a proof
  accepted with no doomed boundary prefix is one from whose extracted words a witness is read.

## The proof

A potential on the oracle's ordered log (`pot`, `LeanerVM.Protocol.Compile.Rom.Potential`):
`1` once some answer collided with or predicted a referenced digest (`Fail`), otherwise the sum,
over the groups of challenges the log has started from doomed boundaries, of their escape
probabilities conditioned on the challenges drawn so far, capped at `1`. It vanishes on the
empty log (`pot_nil`), rises by at most `εmax + (4 + k)(|ℓ| + 1)/2^256` in expectation at each
fresh query (`step_ineq`), and is `1` on every reachable final log on which the verifier accepts
with a doomed boundary prefix (`final_ineq`, through `verify_of_mem_support_logExperiment`).
The engine `prEvent_romExperiment_le_of_logFreshStepBelow` (`LeanerVM.Protocol.ToVCVio.Rom`)
turns this into the bound.

## Decisions

* The proof-of-work factor is `2^-min(b, 64)`: the predicate `powOk` tests a 64-bit word, so
  for `b > 64` it holds with probability `2^-64`, not `2^-b`. leanVM uses `b = 17`.
* The seeding is a fixed chain of hashes (`Seed`): leanVM's `H(H(ivpre) ‖ pi)` with `ivpre`
  holding `H(bytecode)` is the seed of three steps.
* The bad event reads the final random-oracle cache only (`extractedHistory` of `z.2`), so it
  is a statement about VCVio's `randomOracle`; the order of the log is used only in the proof.
-/

namespace LeanerVM.Protocol.Compile.Rom

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol.Blake2sHash LeanerVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

/-- The failure term: `(4 + k) · N / 2^256`, `k` the number of seeding steps, bounds the
probability that one fresh answer collides with or predicts one of the digests a log of fewer
than `N` entries refers to. -/
noncomputable def failBound (σ : Seed) (N : ℕ) : ℝ≥0∞ :=
  ((4 + σ.steps.length) * N : ℕ) / 2 ^ 256

/-- Some boundary prefix of the extracted history of the verifier's run on `π`, under the
answers of the cache `c`, is doomed. -/
def Doomed {P : Prog Bool} (C : Cert P) (σ : Seed) (π : Proof) (c : HashSpec.QueryCache) :
    Prop :=
  ∃ h₀, h₀ <+: extractedHistory (fun x ↦ c x) σ P π ∧ Boundary h₀ ∧ C.D h₀

/-- **The random-oracle theorem of the compiled verifier.** For a verifier program `P` with a
doom certificate `C`, the seeding `σ`, an adversary `A` making at most `QA` queries and a
compiled verifier making at most `QV` queries on every proof, the probability that the verifier
accepts the adversary's proof while some boundary prefix of its extracted history is doomed is
at most `(QA + QV) · (εmax + failBound σ (QA + QV))`, where `εmax` bounds every escape bound of
the certificate discounted by the proof of work before it. -/
theorem romSound (P : Prog Bool) (C : Cert P) (σ : Seed) (εmax : ℝ≥0∞)
    (hε : ∀ h, (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * C.ε h ≤ εmax)
    (A : OracleComp HashSpec Proof) (QA : ℕ) (hA : IsTotalQueryBound A QA)
    (QV : ℕ) (hV : ∀ π, IsTotalQueryBound (verifierComp σ P π) QV) :
    Pr{let z ← romExperiment A (verifierComp σ P)}[z.1.2 = true ∧ Doomed C σ z.1.1 z.2] ≤
      (QA + QV : ℕ) * (εmax + failBound σ (QA + QV)) := by
  refine prEvent_romExperiment_le_of_logFreshStepBelow (QA + QV) ?_ (pot_nil C.D σ P) A
    (verifierComp σ P) QA QV hA hV le_rfl (Doomed C σ) ?_
  · intro ℓ t hℓ ht
    refine (step_ineq C hε ℓ t ht).trans (add_le_add le_rfl (add_le_add le_rfl ?_))
    rw [failBound, card_digest, Nat.cast_pow, Nat.cast_ofNat]
    refine ENNReal.div_le_div_right ?_ _
    exact_mod_cast Nat.mul_le_mul_left _ hℓ
  · intro z hz hacc hbad
    by_cases hf : Fail σ z.2
    · simp only [pot, hf, ↓reduceIte, le_refl]
    · refine final_ineq C hf (verify_of_mem_support_logExperiment A hz hacc) ?_
      obtain ⟨h₀, hh₀, hb, hD⟩ := hbad
      exact ⟨h₀, hh₀, hb, hD⟩

end
end LeanerVM.Protocol.Compile.Rom
