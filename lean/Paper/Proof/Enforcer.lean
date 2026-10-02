/-
  Lemmas about Algorithm 1 (§2.3): output prefixes grow, and the limit of the
  outer loop is a trace.
-/
import Paper.Enforcer
import Paper.Proof.MFOTL

namespace Paper

variable {Sig : Signature}

namespace Enforcer

variable {Cau Sup : Set Sig.ℰ} (E : Enforcer Sig Cau Sup)

/-! ### Output prefixes grow -/

/-- `σ` is a prefix of `σ'`. -/
def Prefix (σ σ' : Trace Sig) : Prop := ∀ j p, σ.seq.get? j = some p → σ'.seq.get? j = some p

theorem Prefix.refl (σ : Trace Sig) : Prefix σ σ := fun _ _ h => h

theorem Prefix.trans {σ σ' σ'' : Trace Sig} (h : Prefix σ σ') (h' : Prefix σ' σ'') :
    Prefix σ σ'' := fun j p hp => h' j p (h j p hp)

/-- The length of a finite trace. -/
def flen (σ : Trace Sig) : ℕ := match σ.seq with | .fin l => l.length | .inf _ => 0

theorem flen_of_fin {σ : Trace Sig} {l} (hs : σ.seq = .fin l) : flen σ = l.length := by
  unfold flen; rw [hs]

theorem snoc?_spec {σ σ' : Trace Sig} {τ : ℕ} {D : DB Sig} (h : σ.snoc? τ D = some σ') :
    Prefix σ σ' ∧ flen σ' = flen σ + 1 ∧ σ'.seq.get? (flen σ) = some (τ, D) ∧
      (∃ l, σ'.seq = .fin l) := by
  unfold Trace.snoc? at h
  split_ifs at h with hc
  cases h
  have hs := Classical.choose_spec hc.1
  refine ⟨?_, ?_, ?_, ⟨_, rfl⟩⟩
  · intro j p hp
    rw [hs] at hp
    simp only [Trace.snoc, Seq.get?] at hp ⊢
    rw [List.getElem?_append_left]; · exact hp
    exact (List.getElem?_eq_some_iff.1 hp).1
  · rw [flen_of_fin hs]; simp [flen, Trace.snoc]
  · rw [flen_of_fin hs]; simp [Trace.snoc, Seq.get?]

theorem proLoop_spec (ts : List ℕ) (st st' : E.𝒮 × Trace Sig) (h : E.proLoop ts st = some st')
    (hf : ∃ l, st.2.seq = .fin l) :
    Prefix st.2 st'.2 ∧ flen st.2 ≤ flen st'.2 ∧ ∃ l, st'.2.seq = .fin l := by
  induction ts generalizing st with
  | nil => cases h; exact ⟨Prefix.refl _, le_rfl, hf⟩
  | cons t ts ih =>
    obtain ⟨s, σ⟩ := st
    simp only [proLoop] at h
    split at h
    next s' _ => exact ih (s', σ) h hf
    next =>
      obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨p1, l1, _, f1⟩ := snoc?_spec h1
      obtain ⟨p2, l2, f2⟩ := ih _ h2 f1
      exact ⟨p1.trans p2, by simp at l2 ⊢; omega, f2⟩

theorem iter_spec (ρ : Trace Sig) (i : ℕ) (st st' : E.𝒮 × Trace Sig) (h : E.iter ρ i st = some st')
    (hf : ∃ l, st.2.seq = .fin l) :
    Prefix st.2 st'.2 ∧ flen st.2 + 1 ≤ flen st'.2 ∧
      (∃ D, st'.2.seq.get? (flen st.2) = some (ρ.τ i, D)) ∧ ∃ l, st'.2.seq = .fin l := by
  obtain ⟨s, σ⟩ := st
  simp only [iter] at h
  obtain ⟨σ', h1, h2⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨p1, l1, g1, f1⟩ := snoc?_spec h1
  obtain ⟨p2, l2, f2⟩ := E.proLoop_spec _ _ _ h2 f1
  exact ⟨p1.trans p2, by simp at l2 ⊢; omega, ⟨_, p2 _ _ g1⟩, f2⟩

theorem run_spec (ρ : Trace Sig) (k : ℕ) (st : E.𝒮 × Trace Sig) (h : E.run ρ k = some st) :
    k ≤ flen st.2 ∧ ∃ l, st.2.seq = .fin l := by
  induction k generalizing st with
  | zero => cases h; exact ⟨Nat.zero_le _, _, rfl⟩
  | succ k ih =>
    obtain ⟨st0, h0, h1⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hk, hf⟩ := ih st0 h0
    obtain ⟨_, hl, _, hf'⟩ := E.iter_spec ρ k st0 st h1 hf
    exact ⟨by omega, hf'⟩

theorem run_prefix (ρ : Trace Sig) (k m : ℕ) (st st' : E.𝒮 × Trace Sig)
    (h : E.run ρ k = some st) (h' : E.run ρ (k + m) = some st') : Prefix st.2 st'.2 := by
  induction m generalizing st' with
  | zero => simp at h'; rw [h] at h'; cases h'; exact Prefix.refl _
  | succ m ih =>
    rw [← add_assoc] at h'
    obtain ⟨st0, h0, h1⟩ := Option.bind_eq_some_iff.1 h'
    exact (ih st0 h0).trans (E.iter_spec ρ _ st0 st' h1 (E.run_spec ρ _ st0 h0).2).1

theorem run_isSome_le (ρ : Trace Sig) {k m : ℕ} (hkm : k ≤ m) (h : (E.run ρ m).isSome) :
    (E.run ρ k).isSome := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  induction d with
  | zero => exact h
  | succ d ih =>
    apply ih (by omega)
    rw [← add_assoc] at h
    simp only [run] at h
    cases hr : E.run ρ (k + d) <;> simp_all

theorem limitElem_spec (ρ : Trace Sig) (hall : ∀ k, (E.run ρ k).isSome) (j k : ℕ)
    (st : E.𝒮 × Trace Sig) (h : E.run ρ k = some st) (hj : j < flen st.2) :
    st.2.seq.get? j = some (E.limitElem ρ hall j) := by
  have hsome : ∀ m (st : E.𝒮 × Trace Sig), E.run ρ m = some st → j < flen st.2 →
      ∃ p, st.2.seq.get? j = some p := by
    intro m st h hj
    obtain ⟨_, l, hl⟩ := E.run_spec ρ m st h
    simp only [flen, hl] at hj
    exact ⟨l[j], by simp [hl, Seq.get?, hj]⟩
  set stj := (E.run ρ (j + 1)).get (hall _) with hstj
  have hj1 : E.run ρ (j + 1) = some stj := by simp [stj]
  have hlen : j < flen stj.2 := by have := (E.run_spec ρ _ _ hj1).1; omega
  obtain ⟨p, hp⟩ := hsome _ _ hj1 hlen
  have hlim : E.limitElem ρ hall j = p := by simp [limitElem, ← hstj, hp]
  rw [hlim]
  obtain ⟨q, hq⟩ := hsome _ _ h hj
  rcases le_total k (j + 1) with hk | hk
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    have := E.run_prefix ρ k d st stj h (hd ▸ hj1) j q hq
    rw [hp] at this; cases this; exact hq
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    have := E.run_prefix ρ (j + 1) d stj st hj1 h j p hp
    exact this

/-- The limit of the outer loop on an infinite input, as an infinite trace. -/
noncomputable def limit (ρ : Trace Sig) (hρ : ρ.length = ⊤) (hall : ∀ k, (E.run ρ k).isSome) :
    Trace Sig where
  seq := .inf (E.limitElem ρ hall)
  finite := by
    intro i p hp
    simp only [Seq.get?, Option.some.injEq] at hp
    set st := (E.run ρ (i + 1)).get (hall _)
    have h1 : E.run ρ (i + 1) = some st := by simp [st]
    have hl := (E.run_spec ρ _ _ h1).1
    have := E.limitElem_spec ρ hall i (i + 1) st h1 (by omega)
    rw [hp] at this
    exact st.2.finite i p this
  mono := by
    intro i p q hp hq
    simp only [Seq.get?, Option.some.injEq] at hp hq
    set st := (E.run ρ (i + 2)).get (hall _)
    have h1 : E.run ρ (i + 2) = some st := by simp [st]
    have hl := (E.run_spec ρ _ _ h1).1
    have a := E.limitElem_spec ρ hall i (i + 2) st h1 (by omega)
    have b := E.limitElem_spec ρ hall (i + 1) (i + 2) st h1 (by omega)
    rw [hp] at a; rw [hq] at b
    exact st.2.mono i p q a b
  progress := by
    intro _ τ
    obtain ⟨i, p, hp, hτ⟩ := ρ.progress hρ τ
    set st0 := (E.run ρ i).get (hall _)
    have h0 : E.run ρ i = some st0 := by simp [st0]
    set st1 := (E.run ρ (i + 1)).get (hall _)
    have h1 : E.run ρ (i + 1) = some st1 := by simp [st1]
    have hit : E.iter ρ i st0 = some st1 := by
      have := h1; simp only [run, h0, Option.bind_some] at this; exact this
    obtain ⟨_, hl, ⟨D, hD⟩, _⟩ := E.iter_spec ρ i st0 st1 hit (E.run_spec ρ _ _ h0).2
    have := E.limitElem_spec ρ hall (flen st0.2) (i + 1) st1 h1 (by omega)
    rw [hD] at this
    refine ⟨flen st0.2, _, rfl, ?_⟩
    rw [← Option.some.inj this]
    have : ρ.τ i = p.1 := by simp [Trace.τ, hp]
    simpa [this] using hτ

theorem limit_seq (ρ : Trace Sig) (hρ : ρ.length = ⊤) (hall : ∀ k, (E.run ρ k).isSome) :
    (E.limit ρ hρ hall).seq = .inf (E.limitElem ρ hall) := rfl

end Enforcer

end Paper
