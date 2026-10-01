/-
  EnfFlash formalization — correctness of EF tables (paper, Section 3.2):
  a (windowed) `table` with `add {φr} remove {¬φl}` computes
  `φl S_[a,b] φr`, and a `lagged table` computes `●_[a,b] φ`.  Hence the
  let interpretation maintained by the enforcer satisfies `LetSem`.
-/
import Enfflash.EF

namespace Enfflash

universe u
variable {B L D : Type u}

section
variable (σ : Tr B L D) (v₀ : ℕ → D)

theorem mem_sinceStore (φl φr : Fm B L D) (τ' : ℕ) (as : List D) :
    ∀ i, (τ', as) ∈ sinceStore σ v₀ φl φr i ↔
      ∃ j ≤ i, σ.ts j = τ' ∧ σ.sat j (vapp as v₀) φr ∧
        ∀ k, j < k → k ≤ i → σ.sat k (vapp as v₀) φl
  | 0 => by
    simp only [sinceStore, Set.mem_setOf_eq, Nat.le_zero, exists_eq_left]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1.symm, h2, fun k h1 h2 => absurd h2 (by omega)⟩
    · rintro ⟨h1, h2, -⟩; exact ⟨h1.symm, h2⟩
  | i + 1 => by
    simp only [sinceStore, Set.mem_union, Set.mem_setOf_eq, mem_sinceStore φl φr τ' as i]
    constructor
    · rintro (⟨⟨j, hj, h1, h2, h3⟩, hl⟩ | ⟨h1, h2⟩)
      · refine ⟨j, by omega, h1, h2, fun k hk1 hk2 => ?_⟩
        rcases Nat.lt_or_eq_of_le hk2 with hk2 | rfl
        · exact h3 k hk1 (by omega)
        · exact hl
      · exact ⟨i + 1, le_rfl, h1.symm, h2, fun k h1 h2 => absurd h2 (by omega)⟩
    · rintro ⟨j, hj, h1, h2, h3⟩
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact Or.inl ⟨⟨j, by omega, h1, h2, fun k hk1 hk2 => h3 k hk1 (by omega)⟩,
          h3 (i + 1) hj le_rfl⟩
      · exact Or.inr ⟨h1.symm, h2⟩

/-- **Since tables are correct.** -/
theorem since_table_correct (a : ℕ) (b : Option ℕ) (φl φr : Fm B L D) (i : ℕ)
    (as : List D) :
    sinceVal σ v₀ a b φl φr i as ↔ (LBody.since a b φl φr).sem σ i (vapp as v₀) := by
  simp only [sinceVal, LBody.sem, mem_sinceStore]
  constructor
  · rintro ⟨τ', ⟨j, hj, rfl, h2, h3⟩, hI⟩; exact ⟨j, hj, hI, h2, h3⟩
  · rintro ⟨j, hj, hI, h2, h3⟩; exact ⟨_, ⟨j, hj, rfl, h2, h3⟩, hI⟩

/-- **Lagged tables are correct.** -/
theorem prev_table_correct (a : ℕ) (b : Option ℕ) (φ : Fm B L D) (i : ℕ) (as : List D) :
    prevVal σ v₀ a b φ i as ↔ (LBody.prev a b φ).sem σ i (vapp as v₀) := by
  cases i with
  | zero => simp [prevVal, LBody.sem]
  | succ i =>
    simp only [prevVal, LBody.sem, Nat.add_sub_cancel]
    constructor
    · rintro ⟨_, ⟨rfl, h⟩, hI⟩; exact ⟨by omega, hI, h⟩
    · rintro ⟨-, hI, h⟩; exact ⟨_, ⟨rfl, h⟩, hI⟩

/-- The let interpretation of the enforcer: present lets and aggregations
    are evaluated directly, temporal lets are read from their tables. -/
def TablesComputeLets (Γ : L → Option (LetDef B L D)) : Prop :=
  ∀ p d, Γ p = some d → ∀ i (as : List D), as.length = d.arity →
    match d.body with
    | .now φ => σ.lv i p as ↔ σ.sat i (vapp as v₀) φ
    | .since a b φl φr => σ.lv i p as ↔ sinceVal σ v₀ a b φl φr i as
    | .prev a b φ => σ.lv i p as ↔ prevVal σ v₀ a b φ i as
    | .agg k ω ts ys φ => σ.lv i p as ↔ (LBody.agg k ω ts ys φ).sem σ i (vapp as v₀)

theorem letSem_of_tables {Γ : L → Option (LetDef B L D)} (h : TablesComputeLets σ v₀ Γ) :
    LetSem Γ σ v₀ := by
  intro p d hd i as hlen
  have := h p d hd i as hlen
  cases hb : d.body with
  | now φ => rw [hb] at this; exact this
  | since a b φl φr => rw [hb] at this; exact this.trans (since_table_correct σ v₀ ..)
  | prev a b φ => rw [hb] at this; exact this.trans (prev_table_correct σ v₀ ..)
  | agg k ω ts ys φ => rw [hb] at this; exact this

end

end Enfflash
