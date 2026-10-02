/-
  Every variable of the filter and of the effect of a clause in `R` is bound
  by each disjunct of its guard; the structure of the realization closure.
-/
import Paper.Proof.Typing

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-- The variables of `ψ` and `ε` are bound by every `κ ∈ π`. -/
def EClause.Guarded (c : EClause Voc) : Prop :=
  ∀ κ ∈ c.π, c.ψ.fv ∪ Term.varsList c.ε.args ⊆ κ.toFormula.fv

/-- The invariant of Figure 5, relative to the free variables of `φ`. -/
def GuardP (φ : Formula Voc) (𝒞 : CSet Voc) : Prop :=
  ∀ C ∈ 𝒞, ∀ c ∈ C, ∀ κ ∈ c.π, c.ψ.fv ∪ Term.varsList c.ε.args ⊆ κ.toFormula.fv ∪ φ.fv

theorem mem_bigTensor_eq : ∀ {𝒞s : List (CSet Voc)} {C : Set (EClause Voc)}, C ∈ CSet.bigTensor 𝒞s →
    ∃ Cs : List (Set (EClause Voc)), List.Forall₂ (· ∈ ·) Cs 𝒞s ∧ ∀ c ∈ C, ∃ C' ∈ Cs, c ∈ C'
  | [], C, h => by
    simp only [CSet.bigTensor, Set.mem_singleton_iff] at h; subst h
    exact ⟨[], .nil, by simp⟩
  | 𝒞 :: 𝒞s, C, h => by
    obtain ⟨C₁, h₁, C₂, h₂, rfl⟩ := h
    obtain ⟨Cs, hCs, hsub⟩ := mem_bigTensor_eq h₂
    refine ⟨C₁ :: Cs, .cons h₁ hCs, ?_⟩
    rintro c (hc | hc)
    · exact ⟨C₁, by simp, hc⟩
    · obtain ⟨C', h1, h2⟩ := hsub c hc; exact ⟨C', by simp [h1], h2⟩

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | [], [], .nil, b, hb => by simp at hb
  | a :: l, b' :: l', .cons h hs, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, by simp, h⟩
    · obtain ⟨a', h1, h2⟩ := forall₂_mem_right hs b hb; exact ⟨a', by simp [h1], h2⟩

theorem fv_conj_mem {κ : GConj Voc} {γ : GAtom Voc} (h : γ ∈ κ) : γ.toFormula.fv ⊆ κ.toFormula.fv := by
  rw [fv_gconj]; intro x hx; exact ⟨γ, h, hx⟩

section
variable {Ξ : RwSetting Voc} {Γ : LetCtx Voc}

theorem guard_rw {α : Mode} {φ : Formula Voc} {𝒞 : CSet Voc} (h : Rw Ξ Γ α φ 𝒞) : GuardP φ 𝒞 := by
  refine Rw.rec (motive_1 := fun _ φ 𝒞 _ => GuardP φ 𝒞)
    (motive_2 := fun φs 𝒞s _ => List.Forall₂ GuardP φs 𝒞s) ?top ?evC ?evS ?letC ?letS ?neg ?andS ?andC
    ?exC ?exS ?futEv ?futNext ?futNextN .nil (fun _ _ ih ihs => .cons ih ihs) h
  case top => intro C hC c hc; simp at hC; subst hC; simp at hc
  case evC =>
    intro e ts _ C hC c hc κ hκ
    simp at hC; subst hC; simp at hc; subst hc
    simp [GDisj.top] at hκ; subst hκ
    simp [Formula.fv, Effect.args]
  case evS =>
    intro e ts _ C hC c hc κ hκ
    simp at hC; subst hC; simp at hc; subst hc
    simp at hκ; subst hκ
    simp [Formula.fv, Effect.args]
  case letC =>
    intro e ts _ C hC c hc κ hκ
    simp at hC; subst hC; simp at hc; subst hc
    simp [GDisj.top] at hκ; subst hκ
    simp [Formula.fv, Effect.args]
  case letS =>
    intro e ts _ C hC c hc κ hκ
    simp at hC; subst hC; simp at hc; subst hc
    simp at hκ; subst hκ
    simp [Formula.fv, Effect.args]
  case neg => intro _ _ _ _ ih; simpa [GuardP, Formula.fv] using ih
  case andS =>
    intro φs j 𝒞 _ _ _ ih C hC c hc κ hκ
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    have h1 := ih C₀ hC₀ c₀ hc₀ κ hκ
    have h2 : (others φs j).fv ⊆ (bigAnd φs).fv := by
      rw [fv_others]; rintro x ⟨k, -, hx⟩; exact fv_get_sub_bigAnd φs k hx
    simp only [Formula.fv]
    intro x hx
    rcases hx with (hx | hx) | hx
    · rcases h1 (Or.inl hx) with h | h
      · exact Or.inl h
      · exact Or.inr (fv_get_sub_bigAnd φs j h)
    · exact Or.inr (h2 hx)
    · rcases h1 (Or.inr hx) with h | h
      · exact Or.inl h
      · exact Or.inr (fv_get_sub_bigAnd φs j h)
  case andC =>
    intro φs 𝒞s _ _ ih C hC c hc κ hκ
    obtain ⟨Cs, hCs, hsub⟩ := mem_bigTensor_eq hC
    obtain ⟨C', hC', hc'⟩ := hsub c hc
    have key : ∀ {φs : List (Formula Voc)} {𝒞s : List (CSet Voc)} {Cs : List (Set (EClause Voc))},
        List.Forall₂ GuardP φs 𝒞s → List.Forall₂ (· ∈ ·) Cs 𝒞s →
        ∀ C' ∈ Cs, ∃ φ ∈ φs, ∃ 𝒞, GuardP φ 𝒞 ∧ C' ∈ 𝒞 := by
      intro φs 𝒞s Cs h₁ h₂
      induction h₁ generalizing Cs with
      | nil => cases h₂; simp
      | cons hφ _ ih' =>
        cases h₂ with
        | cons hc hcs =>
          intro C' hC'
          rcases List.mem_cons.1 hC' with rfl | hC'
          · exact ⟨_, by simp, _, hφ, hc⟩
          · obtain ⟨φ, h1, 𝒞, h2, h3⟩ := ih' hcs C' hC'; exact ⟨φ, by simp [h1], 𝒞, h2, h3⟩
    obtain ⟨φ, hφ, 𝒞, hg, hm⟩ := key ih hCs C' hC'
    have hfv : φ.fv ⊆ (bigAnd φs).fv := by rw [fv_bigAnd]; intro x hx; exact ⟨φ, hφ, hx⟩
    exact (hg C' hm c hc' κ hκ).trans (Set.union_subset_union_right _ hfv)
  case exC =>
    intro x φ 𝒞 _ hsub ih C hC c hc κ' hκ'
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    obtain ⟨hπ, hψ⟩ := hsub C₀ hC₀ c₀ hc₀
    obtain ⟨π', hπ'⟩ := Option.isSome_iff_exists.1 hπ
    obtain ⟨ψ', hψ'⟩ := Option.isSome_iff_exists.1 hψ
    simp only [hπ', hψ', Option.getD_some] at hκ' ⊢
    have h2 := mapM_forall₂ hπ'
    obtain ⟨κ, hκ, hκκ'⟩ := forall₂_mem_right h2 κ' hκ'
    replace hκκ' := mapM_forall₂ hκκ'
    have hk := (GConj.subst_spec hκκ').1
    have hψf := (Formula.subst_spec _ _ _ _ hψ').1
    have h1 := ih C₀ hC₀ c₀ hc₀ κ hκ
    rw [hk, hψf, Effect.subst_args, Term.varsList_subst]
    simp only [Formula.fv]
    rintro y (⟨hy, hyx⟩ | ⟨hy, hyx⟩)
    · rcases h1 (Or.inl hy) with h | h
      · exact Or.inl ⟨h, hyx⟩
      · exact Or.inr ⟨h, hyx⟩
    · rcases h1 (Or.inr hy) with h | h
      · exact Or.inl ⟨h, hyx⟩
      · exact Or.inr ⟨h, hyx⟩
  case exS =>
    intro x φ 𝒞 _ ih C hC c' hc' κ' hκ'
    obtain ⟨C₀, hC₀, -, rfl⟩ := hC
    rcases c' with ⟨π', ψ', ε'⟩
    obtain ⟨c, hc, ht, hε⟩ := hc'
    simp only at hε hκ' ht ⊢; subst hε
    simp only [Formula.fv]
    cases ht with
    | bound hb =>
      have h1 := ih C₀ hC₀ c hc κ' hκ'
      have hx := Binds.mem_fv (hb κ' hκ')
      intro y hy
      rcases h1 hy with h | h
      · exact Or.inl h
      · by_cases hyx : y = x
        · subst hyx; exact Or.inl hx
        · exact Or.inr ⟨h, hyx⟩
    | @filter π₀ ψ'' hg =>
      simp only [GDisj.prod, List.mem_flatMap, List.mem_map] at hκ'
      obtain ⟨κ, hκ, κ₀, hκ₀, rfl⟩ := hκ'
      have h1 := ih C₀ hC₀ c hc κ hκ
      have hx : x ∈ (κ ++ κ₀).toFormula.fv := by
        rw [fv_gconj]
        obtain ⟨γ, hγ, hb⟩ := (hg.sound.1 κ₀ hκ₀ x rfl)
        have := Binds.mem_fv (⟨γ, hγ, hb⟩ : κ₀.Binds x)
        rw [fv_gconj] at this
        obtain ⟨γ', h', h''⟩ := this
        exact ⟨γ', List.mem_append_right _ h', h''⟩
      have hsubκ : κ.toFormula.fv ⊆ (κ ++ κ₀).toFormula.fv := by
        rw [fv_gconj, fv_gconj]; rintro y ⟨γ, hγ, hy⟩; exact ⟨γ, List.mem_append_left _ hγ, hy⟩
      intro y hy
      have hy' : y ∈ c.ψ.fv ∪ Term.varsList c.ε.args := by
        rcases hy with hy | hy
        · exact Or.inl (hg.fv_filter hy)
        · exact Or.inr hy
      rcases h1 hy' with h | h
      · exact Or.inl (hsubκ h)
      · by_cases hyx : y = x
        · subst hyx; exact Or.inl hx
        · exact Or.inr ⟨h, hyx⟩
  case futEv =>
    intro a b h φ 𝒞 _ _ ih C hC c' hc' κ hκ
    obtain ⟨C₀, ⟨hC₀, -, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, hπ, hψ⟩ := hun c hc
    have h1 := ih C₀ hC₀ c hc [] (by rw [hπ]; simp [GDisj.top])
    simp only [GDisj.top, List.mem_singleton] at hκ; subst hκ
    simp only [hε, deferEffect, Effect.args, Formula.fv] at h1 ⊢
    intro y hy; rcases hy with hy | hy
    · exact absurd hy (Set.notMem_empty _)
    · exact h1 (Or.inr hy)
  case futNext =>
    intro b φ 𝒞 _ _ ih C hC c' hc' κ hκ
    obtain ⟨C₀, ⟨hC₀, -, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, hπ, hψ⟩ := hun c hc
    have h1 := ih C₀ hC₀ c hc [] (by rw [hπ]; simp [GDisj.top])
    simp only [GDisj.top, List.mem_singleton] at hκ; subst hκ
    simp only [hε, deferEffect, Effect.args, Formula.fv] at h1 ⊢
    intro y hy; rcases hy with hy | hy
    · exact absurd hy (Set.notMem_empty _)
    · exact h1 (Or.inr hy)
  case futNextN =>
    intro n φ 𝒞 _ _ ih C hC c' hc' κ hκ
    obtain ⟨C₀, ⟨hC₀, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, hπ, hψ⟩ := hun c hc
    have h1 := ih C₀ hC₀ c hc [] (by rw [hπ]; simp [GDisj.top])
    simp only [GDisj.top, List.mem_singleton] at hκ; subst hκ
    simp only [hε, deferEffect, Effect.args, Formula.fv, fv_nextN] at h1 ⊢
    intro y hy; rcases hy with hy | hy
    · exact absurd hy (Set.notMem_empty _)
    · exact h1 (Or.inr hy)

end

end Paper
