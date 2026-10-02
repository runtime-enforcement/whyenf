/-
  Proof of Lemma 4.2 (guard extraction).
-/
import Paper.Claims
import Paper.Guards
import Paper.Proof.MFOTL

namespace Paper

variable {Voc : Vocabulary}

theorem Guards_spec {m X Φ π φ} (h : Guards (Voc := Voc) m X Φ = some (π, φ)) :
    GX m .pos X Φ π φ := by
  unfold Guards at h
  split_ifs at h with hex
  have := Classical.choose_spec hex
  rw [Option.some.inj h] at this
  exact this

section sem
variable (σ : Str Voc.toSignature) (v : Val Voc) (i : ℕ)

@[simp] theorem sat_or (φ ψ : Formula Voc) : (Formula.or φ ψ).sat σ v i ↔ φ.sat σ v i ∨ ψ.sat σ v i := by
  simp only [Formula.or, Formula.sat]; tauto

@[simp] theorem sat_imp (φ ψ : Formula Voc) : (Formula.imp φ ψ).sat σ v i ↔ (φ.sat σ v i → ψ.sat σ v i) := by
  simp only [Formula.imp, sat_or, Formula.sat]; tauto

@[simp] theorem sat_bot : (Formula.bot : Formula Voc).sat σ v i ↔ False := by
  simp [Formula.bot, Formula.sat]

theorem sat_conj (κ : GConj Voc) : κ.toFormula.sat σ v i ↔ ∀ γ ∈ κ, γ.toFormula.sat σ v i := by
  induction κ with
  | nil => simp [GConj.toFormula, Formula.sat]
  | cons γ κ ih =>
    simp only [GConj.toFormula, List.foldr_cons, Formula.sat, List.mem_cons, forall_eq_or_imp] at ih ⊢
    rw [ih]

theorem sat_disj (π : GDisj Voc) : π.toFormula.sat σ v i ↔ ∃ κ ∈ π, κ.toFormula.sat σ v i := by
  induction π with
  | nil => simp [GDisj.toFormula]
  | cons κ π ih => simp [GDisj.toFormula] at ih ⊢; rw [ih]

theorem sat_prod (π₁ π₂ : GDisj Voc) :
    (π₁.prod π₂).toFormula.sat σ v i ↔ π₁.toFormula.sat σ v i ∧ π₂.toFormula.sat σ v i := by
  simp only [sat_disj, GDisj.prod, List.mem_flatMap, List.mem_map, sat_conj]
  constructor
  · rintro ⟨κ, ⟨κ₁, h₁, κ₂, h₂, rfl⟩, h⟩
    exact ⟨⟨κ₁, h₁, fun γ hγ => h γ (List.mem_append_left _ hγ)⟩,
      ⟨κ₂, h₂, fun γ hγ => h γ (List.mem_append_right _ hγ)⟩⟩
  · rintro ⟨⟨κ₁, h₁, a⟩, ⟨κ₂, h₂, b⟩⟩
    refine ⟨κ₁ ++ κ₂, ⟨κ₁, h₁, κ₂, h₂, rfl⟩, fun γ hγ => ?_⟩
    rcases List.mem_append.1 hγ with h | h
    · exact a γ h
    · exact b γ h

theorem sat_append (π₁ π₂ : GDisj Voc) :
    (π₁ ++ π₂).toFormula.sat σ v i ↔ π₁.toFormula.sat σ v i ∨ π₂.toFormula.sat σ v i := by
  simp only [sat_disj, List.mem_append]
  constructor
  · rintro ⟨κ, h | h, hs⟩
    · exact Or.inl ⟨κ, h, hs⟩
    · exact Or.inr ⟨κ, h, hs⟩
  · rintro (⟨κ, h, hs⟩ | ⟨κ, h, hs⟩)
    · exact ⟨κ, Or.inl h, hs⟩
    · exact ⟨κ, Or.inr h, hs⟩

end sem

/-- The meaning of `m ⊢ Φ ⇝^p_X (π, φ)`: `⋁π ∧ φ ≡ Φ` for `p = +`, and
    `⋁π → φ ≡ Φ` for `p = −` (the dual equation of l.1188). -/
def GXMeaning : Pol → GDisj Voc → Formula Voc → Formula Voc → Prop
  | .pos, π, φ, Φ => Equiv (.and π.toFormula φ) Φ
  | .neg, π, φ, Φ => Equiv (.imp π.toFormula φ) Φ

theorem GX.sound {m : Set Voc.ℰ} {p X Φ π φ} (h : GX m p X Φ π φ) :
    (∀ κ ∈ π, ∀ x ∈ X, κ.Binds x) ∧ GXMeaning p π φ Φ := by
  induction h with
  | none p Φ =>
    refine ⟨fun _ _ x hx => absurd hx (Set.notMem_empty x), ?_⟩
    cases p <;> intro σ v i <;> simp [Formula.sat, sat_disj, sat_conj]
  | vac X =>
    exact ⟨by simp, fun σ v i => by simp [Formula.sat, sat_disj]⟩
  | pred X p ts _ hX =>
    refine ⟨?_, fun σ v i => ?_⟩
    · intro κ hκ x hx
      simp only [List.mem_singleton] at hκ; subst hκ
      exact ⟨_, List.mem_singleton_self _, Or.inl ⟨p, ts, rfl, hX x hx⟩⟩
    · simp [Formula.sat, sat_disj, sat_conj, GAtom.toFormula]
  | eq X x c hX =>
    refine ⟨?_, fun σ v i => ?_⟩
    · intro κ hκ y hy
      simp only [List.mem_singleton] at hκ; subst hκ
      have : y = x := hX hy
      subst this
      exact ⟨_, List.mem_singleton_self _, Or.inr ⟨c, rfl⟩⟩
    · simp [Formula.sat, sat_disj, sat_conj, GAtom.toFormula]
  | andPos _ _ hX ih₁ ih₂ =>
    refine ⟨?_, fun σ v i => ?_⟩
    · intro κ hκ x hx
      simp only [GDisj.prod, List.mem_flatMap, List.mem_map] at hκ
      obtain ⟨κ₁, h₁, κ₂, h₂, rfl⟩ := hκ
      rcases hX hx with hx | hx
      · obtain ⟨γ, hγ, hb⟩ := ih₁.1 κ₁ h₁ x hx
        exact ⟨γ, List.mem_append_left _ hγ, hb⟩
      · obtain ⟨γ, hγ, hb⟩ := ih₂.1 κ₂ h₂ x hx
        exact ⟨γ, List.mem_append_right _ hγ, hb⟩
    · have e₁ := ih₁.2 σ v i; have e₂ := ih₂.2 σ v i
      simp only [Formula.sat, sat_prod] at e₁ e₂ ⊢
      rw [← e₁, ← e₂]; tauto
  | andNeg _ _ ih₁ ih₂ =>
    refine ⟨?_, fun σ v i => ?_⟩
    · intro κ hκ x hx
      rcases List.mem_append.1 hκ with h | h
      · exact ih₁.1 κ h x hx
      · exact ih₂.1 κ h x hx
    · have e₁ := ih₁.2 σ v i; have e₂ := ih₂.2 σ v i
      simp only [Formula.sat, sat_imp, sat_append] at e₁ e₂ ⊢
      rw [← e₁, ← e₂]; tauto
  | @neg p X φ φ' π _ ih =>
    refine ⟨ih.1, ?_⟩
    cases p
    · intro σ v i
      have e := ih.2 σ v i
      simp only [Formula.sat, sat_imp] at e ⊢; rw [← e]; tauto
    · intro σ v i
      have e := ih.2 σ v i
      simp only [Formula.sat, sat_imp] at e ⊢; rw [← e]; tauto

theorem lemma_4_2 {m : Set Voc.ℰ} {X : Set Voc.𝕍} {Φ φ : Formula Voc} {π : GDisj Voc}
    (h : Guards m X Φ = some (π, φ)) :
    (∀ κ ∈ π, ∀ x ∈ X, κ.Binds x) ∧ Equiv (.and π.toFormula φ) Φ :=
  (Guards_spec h).sound


theorem lemma_4_2_holds : Lemma_4_2 Voc := lemma_4_2

end Paper
