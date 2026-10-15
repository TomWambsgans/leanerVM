/-
  LeanerVM.Protocol.Compile.Rom.Known

  The decoding of a log without failure is stable: a digest decoded once keeps its decoding in
  every longer prefix, a chain step from a decoded state is read by the decoder at its entry,
  and the seed is decoded at the entry that completes the seeding.
-/

module

public import LeanerVM.Protocol.Compile.Rom.Potential

/-!
# Stability of the decoding without failure

`LeanerVM.Protocol.Compile.Rom.Decode` reads a log entry by entry. In a log without failure
(`Fail`), that reading agrees with the compiled verifier's run: this module proves the three
facts the final inequality (`LeanerVM.Protocol.Compile.Rom.Final`) uses.

* `Known σ P ℓ c inf`: the digest `c` is the output of an entry of `ℓ`, and every prefix of `ℓ`
  past that entry decodes `c` as `inf`. Once a digest is decoded its decoding is fixed
  (`known_of_set`): only an entry with output `c` could change it, and outputs are distinct.
* `entry_read`: if `cv` is `Known` and the `j`-th entry is the chain step `cv ‖ (x, tag)`, the
  decoder reads that entry with `cv`'s decoding: its record is among the log's records, and the
  output's decoding is `Known`. The entry comes after `cv`'s (`lt_of_chunk`), and once a digest
  is decoded the seeding is complete (`pend_none_of_info`), so the entry is not read as seeding.
* `seed_known`: if the seeding computes the seed `s₀` through the log's answers, some entry
  completes it, the record `bnd [] P` of `s₀` is among the log's records, and `s₀`'s decoding is
  `Known`. The seeding's entries come in order (`lt_of_seedInput`).
-/

namespace LeanerVM.Protocol.Compile.Rom

open LeanerVM.Parameters LeanerVM.Semantics LeanerVM.Protocol.Blake2sHash LeanerVM.Protocol.Rom

@[expose] public section

variable {σ : Seed} {P : Prog Bool}

/-! ## Recording decodings -/

theorem setInfo_eq_some {f : Digest → Option Info} {u c : Digest} {o : Option Info} {i : Info}
    (h : setInfo f u o c = some i) : (c = u ∧ o = some i) ∨ f c = some i := by
  rcases o with _ | j
  · exact Or.inr h
  · simp only [setInfo, Function.update_apply] at h
    split at h
    · exact Or.inl ⟨by assumption, h⟩
    · exact Or.inr h

theorem setInfo_of_ne {f : Digest → Option Info} {u c : Digest} (o : Option Info) (h : c ≠ u) :
    setInfo f u o c = f c := by
  rcases o with _ | j
  · rfl
  · simp [setInfo, h]

theorem setInfo_self (f : Digest → Option Info) (u : Digest) {i : Info} :
    setInfo f u (some i) u = some i := by
  simp [setInfo]

/-- A decoded digest is the output of an entry. -/
theorem info_output (σ : Seed) (P : Prog Bool) (ℓ' : Log) {c : Digest} {i : Info}
    (h : (decode σ P ℓ').info c = some i) : ∃ (m : ℕ) (hm : m < ℓ'.length), ℓ'[m].2 = c := by
  induction ℓ' using List.reverseRecOn generalizing i with
  | nil => simp [Dec.init] at h
  | append_singleton ℓ e ih =>
    obtain ⟨t, u⟩ := e
    rw [info_decode_append] at h
    rcases setInfo_eq_some h with ⟨rfl, -⟩ | h
    · exact ⟨ℓ.length, by simp, by simp⟩
    · obtain ⟨m, hm, hmc⟩ := ih h
      exact ⟨m, by simp; omega, by rw [List.getElem_append_left hm]; exact hmc⟩

theorem decode_take_succ (σ : Seed) (P : Prog Bool) (ℓ : Log) {j : ℕ} (hj : j < ℓ.length) :
    decode σ P (ℓ.take (j + 1)) =
      decStep σ P (ℓ.take j) (decode σ P (ℓ.take j)) ℓ[j].1 ℓ[j].2 := by
  rw [← List.take_append_getElem hj]
  exact decode_append σ P _ ℓ[j].1 ℓ[j].2

/-- The records of a log extend the records of every prefix. -/
theorem kinds_prefix (σ : Seed) (P : Prog Bool) (l r : Log) :
    (decode σ P l).kinds <+: (decode σ P (l ++ r)).kinds := by
  induction r using List.reverseRecOn with
  | nil => simp
  | append_singleton r e ih =>
    obtain ⟨t, u⟩ := e
    rw [← List.append_assoc, kinds_decode_append]
    exact ih.trans (List.prefix_append _ _)

theorem kinds_mem_of_take (σ : Seed) (P : Prog Bool) (ℓ : Log) (j : ℕ)
    {κ : Shape × Digest} (h : κ ∈ (decode σ P (ℓ.take j)).kinds) : κ ∈ (decode σ P ℓ).kinds := by
  have := kinds_prefix σ P (ℓ.take j) (ℓ.drop j)
  rw [List.take_append_drop] at this
  exact this.subset h

/-! ## Known digests -/

/-- The digest `c` is the output of an entry of `ℓ`, and every prefix past that entry decodes it
as `inf`. -/
def Known (σ : Seed) (P : Prog Bool) (ℓ : Log) (c : Digest) (inf : Info) : Prop :=
  ∃ (m : ℕ) (hm : m < ℓ.length), ℓ[m].2 = c ∧
    ∀ j, m < j → j ≤ ℓ.length → (decode σ P (ℓ.take j)).info c = some inf

/-- **Decodings are stable without failure.** -/
theorem known_of_set {ℓ : Log} (hf : ¬ Fail σ ℓ) {m : ℕ} (hm : m < ℓ.length) {inf : Info}
    (h : (decode σ P (ℓ.take (m + 1))).info ℓ[m].2 = some inf) : Known σ P ℓ ℓ[m].2 inf := by
  refine ⟨m, hm, rfl, fun j hj hjl ↦ ?_⟩
  induction j, hj using Nat.le_induction with
  | base => exact h
  | succ j hmj ih =>
    have hjl' : j < ℓ.length := by omega
    rw [decode_take_succ σ P ℓ hjl']
    show setInfo _ ℓ[j].2 _ ℓ[m].2 = some inf
    rw [setInfo_of_ne _ (output_ne hf hm hjl' (by omega)), ih (by omega)]

/-! ## The seeding -/

theorem goPend_none_mono {H H' : Bytes → Option Digest}
    (hH : ∀ x v, H x = some v → H' x = some v) :
    ∀ (as : List (Bytes × Bytes)) (d : Digest), goPend H as d = none → goPend H' as d = none
  | [], _, _ => rfl
  | a :: as, d, h => by
    simp only [goPend] at h ⊢
    split at h
    · simp at h
    · rename_i d' hd
      rw [hH _ _ hd]
      exact goPend_none_mono hH as d' h

theorem pend_none_mono {H H' : Bytes → Option Digest} (hH : ∀ x v, H x = some v → H' x = some v)
    {σ : Seed} (h : pend H σ = none) : pend H' σ = none := by
  simp only [pend] at h ⊢
  split at h
  · simp at h
  · rename_i d hd
    rw [hH _ _ hd]
    exact goPend_none_mono hH _ _ h

theorem goPend_unanswered {H : Bytes → Option Digest} :
    ∀ (as : List (Bytes × Bytes)) (d : Digest) {x : Bytes} {b : Bool},
      goPend H as d = some (x, b) → H x = none
  | [], _, _, _, h => by simp [goPend] at h
  | a :: as, d, x, b, h => by
    simp only [goPend] at h
    split at h
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact hn
    · exact goPend_unanswered as _ h

theorem pend_unanswered {H : Bytes → Option Digest} {σ : Seed} {x : Bytes} {b : Bool}
    (h : pend H σ = some (x, b)) : H x = none := by
  simp only [pend] at h
  split at h
  · rename_i hn
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hn
  · exact goPend_unanswered _ _ h

theorem goPend_complete {H H' : Bytes → Option Digest} (hH : ∀ x v, H x = some v → H' x = some v)
    {x : Bytes} {u : Digest} (hx : H' x = some u) :
    ∀ (as : List (Bytes × Bytes)) (d : Digest), goPend H as d = some (x, true) →
      goPend H' as d = none
  | [], _, h => by simp [goPend] at h
  | a :: as, d, h => by
    simp only [goPend] at h ⊢
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq, List.isEmpty_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [hx]; rfl
    · rename_i d' hd
      rw [hH _ _ hd]
      exact goPend_complete hH hx as d' h

theorem pend_complete {H H' : Bytes → Option Digest} (hH : ∀ x v, H x = some v → H' x = some v)
    {σ : Seed} {x : Bytes} {u : Digest} (hx : H' x = some u) (h : pend H σ = some (x, true)) :
    pend H' σ = none := by
  simp only [pend] at h ⊢
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq, List.isEmpty_iff] at h
    obtain ⟨rfl, hs⟩ := h
    rw [hx]
    simp only [hs, goPend]
  · rename_i d hd
    rw [hH _ _ hd]
    exact goPend_complete hH hx _ _ h

theorem stepAt_info_none (ℓ : Log) (cv : Digest) (x : E) (tag : ℕ) (u : Digest) :
    (stepAt ℓ cv x tag none).2 u = none := rfl

theorem look_mono_append (ℓ : Log) (t : Bytes) (u : Digest) :
    ∀ x v, look ℓ x = some v → look (ℓ ++ [(t, u)]) x = some v :=
  fun _ _ h ↦ look_append_of_some h _

/-- Once a digest is decoded, the seeding is answered. -/
theorem pend_none_of_info (σ : Seed) (P : Prog Bool) (ℓ' : Log)
    (h : ∃ c i, (decode σ P ℓ').info c = some i) : pend (look ℓ') σ = none := by
  induction ℓ' using List.reverseRecOn with
  | nil => obtain ⟨c, i, h⟩ := h; simp [Dec.init] at h
  | append_singleton ℓ e ih =>
    obtain ⟨t, u⟩ := e
    obtain ⟨c, i, h⟩ := h
    rw [info_decode_append] at h
    rcases setInfo_eq_some h with ⟨-, hs⟩ | h
    · unfold step at hs
      split at hs
      · rename_i hp
        exact pend_complete (look_mono_append ℓ t u)
          (look_append_single_self (pend_unanswered hp) u) hp
      · split at hs
        · rename_i cv x tag _
          rcases ho : (decode σ P ℓ).info cv with _ | j
          · rw [ho] at hs; simp [stepAt_info_none] at hs
          · exact pend_none_mono (look_mono_append ℓ t u) (ih ⟨cv, j, ho⟩)
        · simp at hs
    · exact pend_none_mono (look_mono_append ℓ t u) (ih ⟨c, i, h⟩)

/-! ## Reading a chain step -/

/-- **A chain step from a known state is read at its entry.** -/
theorem entry_read {ℓ : Log} (hf : ¬ Fail σ ℓ) {cv : Digest} {inf : Info}
    (hk : Known σ P ℓ cv inf) {j : ℕ} (hj : j < ℓ.length) {x : E} {tag : ℕ} (htag : tag < 256)
    (ht : ℓ[j].1 = digestBytes cv ++ blockOf x tag) :
    ((stepAt (ℓ.take j) cv x tag (some inf)).1, ℓ[j].2) ∈ (decode σ P ℓ).kinds ∧
      ∀ inf', (stepAt (ℓ.take j) cv x tag (some inf)).2 ℓ[j].2 = some inf' →
        Known σ P ℓ ℓ[j].2 inf' := by
  obtain ⟨m, hm, hmc, hall⟩ := hk
  have hmj : m < j := lt_of_chunk hf hm hj (Or.inl (by rw [ht, hmc]; exact chunk0_append _ _))
  have hinfo : (decode σ P (ℓ.take j)).info cv = some inf := hall j hmj hj.le
  have hpend : pend (look (ℓ.take j)) σ = none := pend_none_of_info σ P _ ⟨cv, inf, hinfo⟩
  have hstep : step σ P (ℓ.take j) (decode σ P (ℓ.take j)) ℓ[j].1 =
      stepAt (ℓ.take j) cv x tag (some inf) := by
    unfold step
    rw [hpend, ht, parse_chain cv x htag]
    simp only [reduceCtorEq, ↓reduceIte, hinfo]
  have hdec := decode_take_succ σ P ℓ hj
  refine ⟨?_, fun inf' hi ↦ ?_⟩
  · refine kinds_mem_of_take σ P ℓ (j + 1) ?_
    rw [hdec]
    show _ ∈ (decode σ P (ℓ.take j)).kinds ++ [((step σ P _ _ ℓ[j].1).1, ℓ[j].2)]
    rw [hstep]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · refine known_of_set hf hj ?_
    rw [hdec]
    show setInfo _ ℓ[j].2 ((step σ P _ _ ℓ[j].1).2 ℓ[j].2) ℓ[j].2 = some inf'
    rw [hstep, hi, setInfo_self]

/-! ## The seed -/

/-- The seeding's remaining steps, answered through the log, end at an entry that the entries
before it leave as the last pending step. -/
theorem goPend_entry {ℓ : Log} (hf : ¬ Fail σ ℓ) {s₀ : Digest} :
    ∀ (as : List (Bytes × Bytes)), (∀ a ∈ as, a ∈ σ.steps) → as ≠ [] →
      ∀ (d : Digest) (m : ℕ) (hm : m < ℓ.length), ℓ[m].2 = d →
        as.foldlM (fun d a ↦ look ℓ (Seed.input a d)) d = some s₀ →
          ∃ (j : ℕ) (hj : j < ℓ.length), m < j ∧ ℓ[j].2 = s₀ ∧
            goPend (look (ℓ.take j)) as d = some (ℓ[j].1, true)
  | [], _, hne, _, _, _, _, _ => absurd rfl hne
  | a :: as, has, _, d, m, hm, hmd, hfold => by
    simp only [List.foldlM_cons, bind, Option.bind_eq_some_iff] at hfold
    obtain ⟨d', hd', hfold⟩ := hfold
    obtain ⟨m', hm', hem', hn'⟩ := (look_eq_some_iff ℓ _ d').mp hd'
    have hmm' : m < m' := lt_of_seedInput hf hm hm' (has a List.mem_cons_self)
      (by rw [hem', hmd])
    rcases as with _ | ⟨a₁, as₁⟩
    · simp only [List.foldlM_nil, pure, Option.some.injEq] at hfold
      refine ⟨m', hm', hmm', by rw [hem', hfold], ?_⟩
      simp only [goPend, hem', hn', List.isEmpty_nil]
    · obtain ⟨j, hj, hm'j, hjs, hg⟩ := goPend_entry hf (a₁ :: as₁)
        (fun b hb ↦ has b (List.mem_cons_of_mem _ hb)) (List.cons_ne_nil _ _) d' m' hm'
        (by rw [hem']) hfold
      refine ⟨j, hj, hmm'.trans hm'j, hjs, ?_⟩
      simp only [goPend]
      rw [look_take_of_first hm' hem' hn' hm'j]
      exact hg

/-- **The seed's entry.** If the seeding computes `s₀` through the log's answers, some entry
outputs `s₀` while the entries before it leave its input as the last pending input. -/
theorem seed_entry {ℓ : Log} (hf : ¬ Fail σ ℓ) {s₀ : Digest} (hs : σ.run (look ℓ) = some s₀) :
    ∃ (j : ℕ) (hj : j < ℓ.length), ℓ[j].2 = s₀ ∧
      pend (look (ℓ.take j)) σ = some (ℓ[j].1, true) := by
  simp only [Seed.run, bind, Option.bind_eq_some_iff] at hs
  obtain ⟨d, hd, hfold⟩ := hs
  obtain ⟨m, hm, hem, hn⟩ := (look_eq_some_iff ℓ _ d).mp hd
  rcases hsteps : σ.steps with _ | ⟨a, as⟩
  · rw [hsteps] at hfold
    simp only [List.foldlM_nil, pure, Option.some.injEq] at hfold
    refine ⟨m, hm, by rw [hem, hfold], ?_⟩
    simp only [pend, hem, hn, hsteps, List.isEmpty_nil]
  · rw [hsteps] at hfold
    obtain ⟨j, hj, hmj, hjs, hg⟩ := goPend_entry hf (a :: as)
      (fun b hb ↦ by rw [hsteps]; exact hb) (List.cons_ne_nil _ _) d m hm (by rw [hem]) hfold
    refine ⟨j, hj, hjs, ?_⟩
    simp only [pend]
    rw [look_take_of_first hm hem hn hmj, hsteps]
    exact hg

/-- **The seed is decoded.** If the seeding computes `s₀` through the log's answers, the
record `bnd [] P` of `s₀` is among the log's records and `s₀`'s decoding is known. -/
theorem seed_known {ℓ : Log} (hf : ¬ Fail σ ℓ) {s₀ : Digest} (hs : σ.run (look ℓ) = some s₀) :
    (Shape.bnd [] P, s₀) ∈ (decode σ P ℓ).kinds ∧
      ∀ inf, stInfo [] P = some inf → Known σ P ℓ s₀ inf := by
  obtain ⟨j, hj, hjs, hp⟩ := seed_entry hf hs
  have hstep : step σ P (ℓ.take j) (decode σ P (ℓ.take j)) ℓ[j].1 =
      (.bnd [] P, fun _ ↦ stInfo [] P) := by
    unfold step
    rw [hp]
    simp
  have hdec := decode_take_succ σ P ℓ hj
  subst hjs
  refine ⟨?_, fun inf hi ↦ ?_⟩
  · refine kinds_mem_of_take σ P ℓ (j + 1) ?_
    rw [hdec]
    show _ ∈ (decode σ P (ℓ.take j)).kinds ++ [((step σ P _ _ ℓ[j].1).1, ℓ[j].2)]
    rw [hstep]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · refine known_of_set hf hj ?_
    rw [hdec]
    show setInfo _ ℓ[j].2 ((step σ P _ _ ℓ[j].1).2 ℓ[j].2) ℓ[j].2 = some inf
    rw [hstep]
    simp only [hi, setInfo_self]

end
end LeanerVM.Protocol.Compile.Rom
