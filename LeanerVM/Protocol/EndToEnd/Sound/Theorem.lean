/-
  LeanerVM.Protocol.EndToEnd.Sound.Theorem

  The end-to-end, random-oracle-model knowledge soundness of leanVM's deployed verifier, at
  `2^-128` per oracle query: the doom bound, the extractor, the knowledge statement, the
  execution it gives, and the numeric bound.
-/

module

public import LeanerVM.Protocol.EndToEnd.Sound.Assemble
public import LeanerVM.Protocol.EndToEnd.Sound.Runs
public import LeanerVM.Protocol.EndToEnd.Execution
public import LeanerVM.Protocol.Verifier.Cost

/-!
# Knowledge soundness of the leanVM verifier in the random-oracle model

Let `P = leanVmProgram (bytecodeWords prog) (publicDigest input)` be the deployed verifier
program (leanVM `a386121f84292f6fa663aaa3e570c15bc0240ea2`) and `σ = leanVmSeed …` its
Fiat–Shamir seed, with BLAKE2s a random oracle (`romExperiment`), an adversary of `QA` queries,
and the verifier's `13300` (`isTotalQueryBound_leanVm`). With `N = QA + 13300`:

* `leanVm_romSound`: the verifier accepts while some boundary prefix of the extracted history is
  doomed for `leanVmCert` with probability at most `N · (2^-128 + failBound σ N)`.
* `extractStack prog input c π`: **the extractor**. It reads the extracted history of `π` under
  the cache `c`, the announced sizes `(s, ρ)` (the value `readSizes` returned along it; a
  classical choice, unique by `announced_eq`) and the stack's committed word `W₀` (the first
  commitment), and returns a candidate of `W₀` at level 0's Johnson threshold satisfying
  `M3Holds (leanIsaInstance blake2sFlockSpec prog s) input`, if one exists (a classical choice;
  the extractor is a specification of what is extracted, not an algorithm).
* `leanVm_knowledge`: **knowledge soundness**. The verifier accepts while the extractor does not
  return admissible sizes and a stack satisfying `M3Holds` with probability at most the same
  bound. The step "accepted and no good candidate ⇒ doomed" (`doomed_of_not_extracted`): after
  the stack's root the certificate's doom is `CommitDoom` (`leanVmSpec_D_commit`), which is
  "no good candidate".
* `leanVm_execution`: for well-formed bytecode, through `execution_of_extracted`, the witness read
  off the extracted stack represents a valid execution of `prog` on `input`, except with the same
  probability.
* `leanVm_bound_le`: for `QA ≤ 2^64` the bound is at most `2^-63`.

Every statement takes the table sumcheck's identities for leanISA, `fid : TableFidHyp prog
input`, as a hypothesis (`LeanerVM.Protocol.EndToEnd.Sound.Assemble`).
-/

namespace LeanerVM.Protocol.EndToEnd.Sound

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Arithmetization LeanerVM.Protocol
open LeanerVM.Protocol.Compile LeanerVM.Protocol.Compile.Rom LeanerVM.Protocol.Verifier
open LeanerVM.Protocol.LeanIsa LeanerVM.Protocol.Whir.Sound LeanerVM.Protocol.EndToEnd.Front
open LeanerVM.Protocol.EndToEnd.Complete (publicDigest)
open LeanerVM.Protocol.Blake2sHash LeanerVM.Protocol.Rom
open OracleComp OracleSpec
open scoped ENNReal

@[expose] public section

/- The enumeration of `Digest` must never be unfolded by unification. -/
attribute [local irreducible] instFintypeDigest

variable (prog : Program) (input : PublicInput) (fid : TableFidHyp prog input)

/-! ## The doom bound -/

/-- Doom never holds at the empty history: the announced sizes are not at stake. -/
theorem leanVmSpec_D_nil : ¬ (leanVmSpec prog input fid).D [] [] := by
  intro hD
  have hs : (verifyExecution (bytecodeWords prog) (publicDigest input)).retSplit [] = none :=
    retSplit_eq_none_of_after rfl (verifyExecution_ne_ret _ _)
  have h1 : (veSpec prog input fid).D [] [] := (Spec.bindD_none hs).1 hD
  have hs' : (readSizes (bytecodeWords prog)).retSplit [] = none :=
    retSplit_eq_none_of_after rfl (readSizes_ne_ret _)
  exact (Spec.bindD_none hs').1 h1

/-- **The certificate's bound**: every escape bound of `leanVmCert`, discounted by the proof of
work before its group (`2^-min(b, 64)`), is at most `2^-128`. -/
theorem leanVmCert_bound (h : List Ev) :
    (2 : ℝ≥0∞)⁻¹ ^ min (grindBits h) 64 * (leanVmCert prog input fid).ε h ≤ εLean := by
  by_cases hr : (leanVmProgram (bytecodeWords prog) (publicDigest input)).Reachable h
  · rw [min_eq_left (grindBits_le_of_reachable _ _ hr)]
    exact Spec.toCert_bound _ (fun hD ↦ absurd hD (leanVmSpec_D_nil prog input fid)) h
  · simp only [leanVmCert, Spec.toCert_ε, hr, false_and, ↓reduceIte, mul_zero, zero_le]

/-- **The random-oracle theorem of the leanVM verifier.** An adversary of `QA` queries makes the
deployed verifier, with BLAKE2s a random oracle, accept a proof whose extracted history passes
through a doomed boundary with probability at most
`(QA + 13300) · (2^-128 + failBound σ (QA + 13300))`. -/
theorem leanVm_romSound (A : OracleComp HashSpec Proof) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
        (leanVmProgram (bytecodeWords prog) (publicDigest input)))}[z.1.2 = true ∧
      Doomed (leanVmCert prog input fid) (leanVmSeed (bytecodeWords prog) (publicDigest input))
        z.1.1 z.2] ≤
      ((QA + 13300 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 +
        failBound (leanVmSeed (bytecodeWords prog) (publicDigest input)) (QA + 13300)) := by
  have h := romSound _ (leanVmCert prog input fid) _ εLean (leanVmCert_bound prog input fid) A QA
    hA leanVmQueryBound (isTotalQueryBound_leanVm _ _)
  rwa [leanVmQueryBound_eq] at h

/-! ## The doom after the stack's root -/

/-- The doom of `verify_execution` after the announced sizes, at good sizes, right after the
stack's root: the root's postcondition. -/
theorem realSpec_D {s : Sizes} {ρ : ℕ} (hadm : s.Admissible prog)
    (hw : Whir.Admissible (verifierLayout prog s).stackLog ρ)
    (hlb : LayoutBounds (verifierLayout prog s)) {l₁ : List Ev} {e : Ev}
    (hce : (commitStack (verifierLayout prog s).stackLog ρ).after [e] = some (.ret ()))
    (hpost : CommitPost prog input (verifierLayout prog s, ρ) () (l₁ ++ [e])) :
    (realSpec input fid hadm hw hlb).D l₁ [e] := by
  refine (Spec.bindD_some (Prog.retSplit_self hce)).2 ⟨fun _ ↦ ?_, ?_⟩
  · obtain ⟨q₀, rest, hc, -⟩ := Whir.Complete.exists_ladder hw
    exact (commitSpec_D _ _ hc l₁ e).2 hpost
  · exact (restSpec input fid hadm hw hlb).start_D _ hpost

/-- **After the stack's root, the certificate's doom is the root's postcondition**: along a
history where `readSizes` returned a good value `a` and the root was committed by `e`, the
doom holds if no candidate of the root satisfies the relation and the stack's is the only
commitment. -/
theorem leanVmSpec_D_commit {l₁ : List Ev} {a : Verifier.Layout × ℕ}
    (hl₁ : (readSizes (bytecodeWords prog)).after l₁ = some (.ret a)) {s : Sizes}
    (hg : Good prog a s) {e : Ev}
    (hce : (commitStack a.1.stackLog a.2).after [e] = some (.ret ()))
    (hpost : CommitPost prog input a () (l₁ ++ [e])) :
    (leanVmSpec prog input fid).D [] (l₁ ++ [e]) := by
  obtain ⟨lay, ρ⟩ := a
  have hve : (verifyExecution (bytecodeWords prog) (publicDigest input)).after (l₁ ++ [e]) =
      some ((verifyBusBalance lay).bind fun bus ↦ (tablePhase lay bus).bind fun cl ↦
        (Verifier.publicInputPhase lay (publicDigest input)).bind fun pc ↦
        (verifyFlock (blake2sR1csLogSize + lay.tableLogHeights.getD opBlake2s 0)).bind fun x ↦
        (ringSwitch x.1 x.2).bind fun y ↦ verifyStackedOpening lay.stackLog ρ
          (ringSwitchClaim lay y.1 y.2 :: (cl ++ pc).map (·.onStack lay))) := by
    rw [verifyExecution_eq, Prog.after_bind_append _ hl₁]
    exact Prog.after_bind_append _ hce []
  have hs : (verifyExecution (bytecodeWords prog) (publicDigest input)).retSplit (l₁ ++ [e]) =
      none := by
    refine retSplit_eq_none_of_after hve fun u h ↦ ?_
    obtain ⟨b, hb, -⟩ := bind_eq_ret_iff h
    exact verifyBusBalance_ne_ret _ _ hb
  refine (Spec.bindD_none hs).2 ?_
  refine (Spec.bindD_after (Prog.retSplit_of_after _ l₁ [e] hl₁) (List.cons_ne_nil _ _)).2 ?_
  have hex : ∃ s, Good prog (lay, ρ) s := ⟨s, hg⟩
  have hlay : lay = verifierLayout prog hex.choose := hex.choose_spec.1
  simp only [bodySpec, hex, ↓reduceDIte, Spec.congr_D]
  refine realSpec_D prog input fid _ _ _ (by rw [← hlay]; exact hce) ?_
  rw [← hlay]
  exact hpost

/-! ## The extractor -/

open Classical in
/-- The sizes and rate a history announced: the value `(verifierLayout prog s, ρ)` that
`readSizes` returned along a prefix of it (a classical choice; unique, `announced_eq`). -/
noncomputable def announced (hist : List Ev) : Option (Sizes × ℕ) :=
  if h : ∃ p : Sizes × ℕ, ∃ l₁, l₁ <+: hist ∧
      (readSizes (bytecodeWords prog)).after l₁ = some (.ret (verifierLayout prog p.1, p.2)) then
    some h.choose
  else none

/-- A program returns along at most one prefix of a history. -/
theorem ret_prefix_unique {α : Type} {p : Prog α} {l l' hist : List Ev} {a a' : α}
    (h1 : l <+: hist) (h2 : l' <+: hist) (ha : p.after l = some (.ret a))
    (ha' : p.after l' = some (.ret a')) : l = l' := by
  rcases le_total l.length l'.length with hlen | hlen
  · obtain ⟨t, rfl⟩ := List.prefix_of_prefix_length_le h1 h2 hlen
    have ht : t = [] := eq_of_after_ret ha (by rw [ha']; rfl)
    rw [ht, List.append_nil]
  · obtain ⟨t, rfl⟩ := List.prefix_of_prefix_length_le h2 h1 hlen
    have ht : t = [] := eq_of_after_ret ha' (by rw [ha]; rfl)
    rw [ht, List.append_nil]

/-- **The announced sizes are the sizes the run announced.** -/
theorem announced_eq {hist l₁ : List Ev} {a : Verifier.Layout × ℕ} {s : Sizes}
    (hpre : l₁ <+: hist) (hl₁ : (readSizes (bytecodeWords prog)).after l₁ = some (.ret a))
    (ha : a.1 = verifierLayout prog s) : announced prog hist = some (s, a.2) := by
  have hex : ∃ p : Sizes × ℕ, ∃ l₁, l₁ <+: hist ∧
      (readSizes (bytecodeWords prog)).after l₁ = some (.ret (verifierLayout prog p.1, p.2)) :=
    ⟨(s, a.2), l₁, hpre, by rw [hl₁, ← ha]⟩
  simp only [announced, hex, ↓reduceDIte, Option.some.injEq]
  obtain ⟨l', hl'pre, hl'⟩ := hex.choose_spec
  obtain rfl := ret_prefix_unique hl'pre hpre hl' hl₁
  rw [hl₁] at hl'
  simp only [Option.some.injEq, Prog.ret.injEq] at hl'
  have h1 : verifierLayout prog hex.choose.1 = verifierLayout prog s := by rw [← ha, hl']
  have h2 := verifierLayout_injective prog h1
  exact Prod.ext h2 (by rw [hl'])

open Classical in
/-- **The extractor.** From the cache `c` and the proof `π`: the extracted history of the
verifier's run, the sizes `s` and rate `ρ` it announced, and the stack's committed word `W₀`
(its first commitment); a candidate of `W₀` at level 0's Johnson threshold satisfying
`M3Holds (leanIsaInstance blake2sFlockSpec prog s) input`, if one exists. The candidate is a
classical choice: the extractor specifies what is extracted, with no claim of efficiency. -/
noncomputable def extractStack (c : HashSpec.QueryCache) (π : Proof) :
    Option (Σ s : Sizes, Column (leanIsaμ prog s)) :=
  let hist := extractedHistory (fun x ↦ c x) (leanVmSeed (bytecodeWords prog) (publicDigest input))
    (leanVmProgram (bytecodeWords prog) (publicDigest input)) π
  match announced prog hist, firstWord hist with
  | some (s, ρ), some W =>
    if hq : ∃ q ∈ Candidates (leanIsaμ prog s) ρ (thrOf (leanIsaμ prog s) ρ) W,
        M3Holds (leanIsaInstance F₀ prog s) input q then
      some ⟨s, hq.choose⟩
    else none
  | _, _ => none

/-- **The extractor succeeds**: it returns admissible sizes and a stack satisfying the leanISA
relation. -/
def Extracted (c : HashSpec.QueryCache) (π : Proof) : Prop :=
  ∃ (s : Sizes) (q : Column (leanIsaμ prog s)), extractStack prog input c π = some ⟨s, q⟩ ∧
    s.Admissible prog ∧
    M3Holds (leanIsaInstance F₀ prog s) input q

/-! ## Accepted without extraction is doomed -/

/-- The commitments of an announcement followed by one commitment. -/
theorem commits_reads_commit (xs : List E) (ht w : ℕ) (W : Word) :
    commits (xs.map Ev.read ++ [Ev.commit ht w W]) = [(ht, w, W)] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [commits] using ih

/-- **Accepted, and the extractor fails, is doomed**: the prefix of the extracted history up to
the stack's root is a boundary at which the certificate's doom holds. -/
theorem doomed_of_not_extracted {c : HashSpec.QueryCache} {π : Proof}
    (hv : Rom.verify (fun x ↦ c x) (leanVmSeed (bytecodeWords prog) (publicDigest input))
      (leanVmProgram (bytecodeWords prog) (publicDigest input)) π = some true)
    (hne : ¬ Extracted prog input c π) :
    Doomed (leanVmCert prog input fid) (leanVmSeed (bytecodeWords prog) (publicDigest input)) π
      c := by
  set hist := extractedHistory (fun x ↦ c x) (leanVmSeed (bytecodeWords prog) (publicDigest input))
    (leanVmProgram (bytecodeWords prog) (publicDigest input)) π with hhist
  obtain ⟨hafter, hws⟩ := after_extractedHistory (fun x ↦ c x) hv
  rw [← hhist] at hafter hws
  -- The run: the announced sizes, the root, the rest.
  obtain ⟨u, m, m', hm, hve, -⟩ := after_bind_ret hafter
  rw [verifyExecution_eq] at hve
  obtain ⟨a, l₁, r, rfl, hl₁, hbody⟩ := after_bind_ret hve
  obtain ⟨v, r₁, r₂, rfl, hce, -⟩ := after_bind_ret hbody
  obtain ⟨level, rest, W, hc, rfl⟩ := commitStack_after_ret hce
  set e := Ev.commit (levelShape a.1.stackLog level (2 ^ level.fold)).1
    (levelShape a.1.stackLog level (2 ^ level.fold)).2 W with he
  have hpre : l₁ ++ [e] <+: hist := by
    rw [hm]
    exact ⟨r₂ ++ m', by simp⟩
  obtain ⟨s, hg⟩ := good_of_readSizes prog hl₁
  obtain ⟨s', -, -, -, hreads⟩ := readSizes_ret_sizes prog hl₁
  -- The root's shape.
  have hcomm : commits (l₁ ++ [e]) = [((levelShape a.1.stackLog level (2 ^ level.fold)).1,
      (levelShape a.1.stackLog level (2 ^ level.fold)).2, W)] := by
    rw [hreads]; exact commits_reads_commit _ _ _ _
  obtain ⟨q₀, rest', hc', -⟩ := Whir.Complete.exists_ladder hg.2.2.1
  rw [hc] at hc'
  simp only [Option.some.injEq, List.cons.injEq] at hc'
  obtain ⟨rfl, rfl⟩ := hc'
  obtain ⟨-, -, hκ, hR, -⟩ := Whir.Params.deployed_spec_hyps hg.2.2.1 hc
  have hshape : StackShape a.1.stackLog a.2 (l₁ ++ [e]) := by
    have hmem : e ∈ hist := by rw [hm]; simp
    have hWs : WellShaped (2 ^ laneBits) W := by rw [he] at hmem; exact hws _ _ W hmem
    refine ⟨by rw [hcomm]; rfl, W, ?_, hWs⟩
    rw [hcomm]
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq, levelShape, wdOf,
      ↓reduceIte, and_true]
    simp only [code₀, hκ, hR]
  -- The first word.
  have hfw : firstWord (l₁ ++ [e]) = some W := by
    simp [firstWord, hcomm]
  -- No good candidate.
  have hdoom : CommitDoom F₀ prog input thrOf a (l₁ ++ [e]) := by
    refine ⟨s, W, hg.1, hfw, fun q hq hM ↦ hne ?_⟩
    have hann : announced prog hist = some (s, a.2) :=
      announced_eq prog ((List.prefix_append l₁ [e]).trans hpre) hl₁ hg.1
    have hfw' : firstWord hist = some W := by
      rw [hm]
      have := firstWord_append hfw (r₂ ++ m')
      simpa [he] using this
    have hq' : ∃ q ∈ Candidates (leanIsaμ prog s) a.2 (thrOf (leanIsaμ prog s) a.2) W,
        M3Holds (leanIsaInstance F₀ prog s) input q := ⟨q, hq, hM⟩
    refine ⟨s, hq'.choose, ?_, hg.2.1, hq'.choose_spec.2⟩
    simp only [extractStack, ← hhist, hann, hfw', hq', ↓reduceDIte]
  exact ⟨l₁ ++ [e], hpre, by simp [Boundary, he], (leanVmSpec_D_commit prog input fid hl₁ hg
    (by cases v; exact hce) ⟨hdoom, hshape⟩)⟩

/-! ## Knowledge soundness -/

include fid in
/-- **Knowledge soundness of the leanVM verifier in the random-oracle model.** An adversary of
`QA` queries makes the deployed verifier, with BLAKE2s a random oracle, accept a proof from
which `extractStack` does not extract admissible sizes `s` and a stack satisfying
`M3Holds (leanIsaInstance blake2sFlockSpec prog s) input` with probability at most
`(QA + 13300) · (2^-128 + failBound σ (QA + 13300))`. -/
theorem leanVm_knowledge (A : OracleComp HashSpec Proof) (QA : ℕ)
    (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
        (leanVmProgram (bytecodeWords prog) (publicDigest input)))}[z.1.2 = true ∧
      ¬ ∃ (s : Sizes) (q : Column (leanIsaμ prog s)),
        extractStack prog input z.2 z.1.1 =
          some (⟨s, q⟩ : Σ s : Sizes, Column (leanIsaμ prog s)) ∧ s.Admissible prog ∧
        M3Holds (leanIsaInstance F₀ prog s) input q] ≤
      ((QA + 13300 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 +
        failBound (leanVmSeed (bytecodeWords prog) (publicDigest input)) (QA + 13300)) := by
  have h := romSound_of_imp _ (leanVmCert prog input fid) _ εLean (leanVmCert_bound prog input fid)
    A QA hA leanVmQueryBound (isTotalQueryBound_leanVm _ _)
    (fun π c ↦ ¬ Extracted prog input c π)
    (fun _ _ hv hb ↦ doomed_of_not_extracted prog input fid hv hb)
  rwa [leanVmQueryBound_eq] at h

include fid in
/-- **The extracted witness represents a valid execution.** For well-formed bytecode, an
adversary of `QA` queries makes the deployed verifier accept a proof from which `extractStack`
does not extract sizes `s` and a stack `q` whose witness `witnessOf blake2sFlockSpec prog s q`
represents a valid execution of `prog` on `input` with probability at most
`(QA + 13300) · (2^-128 + failBound σ (QA + 13300))`. -/
theorem leanVm_execution (hwf : WellFormedBytecode prog) (A : OracleComp HashSpec Proof)
    (QA : ℕ) (hA : IsTotalQueryBound A QA) :
    Pr{let z ← romExperiment A (verifierComp (leanVmSeed (bytecodeWords prog) (publicDigest input))
        (leanVmProgram (bytecodeWords prog) (publicDigest input)))}[z.1.2 = true ∧
      ¬ ∃ (s : Sizes) (q : Column (leanIsaμ prog s)),
        extractStack prog input z.2 z.1.1 = some (⟨s, q⟩ : Σ s : Sizes, Column (leanIsaμ prog s)) ∧
        ∃ t, AssignmentRepresents (witnessOf F₀ prog s q) t ∧ ValidExecution prog input t] ≤
      ((QA + 13300 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 +
        failBound (leanVmSeed (bytecodeWords prog) (publicDigest input)) (QA + 13300)) := by
  have h := romSound_of_imp _ (leanVmCert prog input fid) _ εLean (leanVmCert_bound prog input fid)
    A QA hA leanVmQueryBound (isTotalQueryBound_leanVm _ _)
    (fun π c ↦ ¬ ∃ (s : Sizes) (q : Column (leanIsaμ prog s)),
        extractStack prog input c π = some ⟨s, q⟩ ∧
        ∃ t, AssignmentRepresents (witnessOf F₀ prog s q) t ∧ ValidExecution prog input t)
    (fun _ _ hv hb ↦ doomed_of_not_extracted prog input fid hv fun ⟨s, q, hx, hs, hM⟩ ↦
      hb ⟨s, q, hx, execution_of_extracted F₀ hwf hs hM⟩)
  rwa [leanVmQueryBound_eq] at h

/-! ## The numbers -/

/-- `2^-k` as `2^(n - k) / 2^n`. -/
theorem inv_pow_eq_div (k n : ℕ) (h : k ≤ n) :
    (2 : ℝ≥0∞)⁻¹ ^ k = ((2 ^ (n - k) : ℕ) : ℝ≥0∞) / ((2 ^ n : ℕ) : ℝ≥0∞) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, ENNReal.div_eq_inv_mul, Nat.cast_pow, Nat.cast_pow,
    Nat.cast_ofNat, pow_add, ENNReal.mul_inv (by simp) (by simp), mul_assoc,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one, ENNReal.inv_pow]

/-- **The numeric bound**: for an adversary of at most `2^64` queries, the bound of the
knowledge statement is at most `2^-63`. -/
theorem leanVm_bound_le (bytecode : List K) (publicInput : Digest) {QA : ℕ} (hQ : QA ≤ 2 ^ 64) :
    ((QA + 13300 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ ^ 128 +
      failBound (leanVmSeed bytecode publicInput) (QA + 13300)) ≤ (2 : ℝ≥0∞)⁻¹ ^ 63 := by
  set N := QA + 13300 with hN
  have hfail : failBound (leanVmSeed bytecode publicInput) N =
      ((6 * N : ℕ) : ℝ≥0∞) / ((2 ^ 256 : ℕ) : ℝ≥0∞) := by
    rw [failBound, Nat.cast_pow, Nat.cast_ofNat]
    rfl
  rw [hfail, inv_pow_eq_div 128 256 (by norm_num), ENNReal.div_add_div_same, ← mul_div_assoc,
    ← Nat.cast_add, ← Nat.cast_mul, inv_pow_eq_div 63 256 (by norm_num)]
  refine ENNReal.div_le_div_right (Nat.cast_le.2 ?_) _
  have hN' : N ≤ 2 ^ 64 + 13300 := by omega
  rw [show 256 - 128 = 128 from rfl, show 256 - 63 = 193 from rfl]
  calc N * (2 ^ 128 + 6 * N) ≤ (2 ^ 64 + 13300) * (2 ^ 128 + 6 * (2 ^ 64 + 13300)) :=
        Nat.mul_le_mul hN' (Nat.add_le_add_left (Nat.mul_le_mul_left 6 hN') _)
    _ ≤ 2 ^ 193 := by norm_num

end
end LeanerVM.Protocol.EndToEnd.Sound
