/-
  Proofs of Appendix A: Lemma A.1, the agreement of Figures 5 and 7, and
  Theorem A.2.
-/
import Paper.TypeSystem
import Paper.Proof.Main

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-! ## Lemma A.1 -/

/-- Figure 4 derivations give guardedness. -/
theorem GX.grd {m : Set Voc.ℰ} {p : Pol} {X : Set Voc.𝕍} {Φ : Formula Voc} {π : GDisj Voc}
    {φ : Formula Voc} (h : GX m p X Φ π φ) : ∀ x ∈ X, Grd m x p Φ := by
  induction h with
  | none => intro x hx; exact absurd hx (Set.notMem_empty _)
  | vac => intro x _; exact .vac
  | pred X p ts hp hX => intro x hx; exact .pred p ts hp (hX x hx)
  | eq X y c hX => intro x hx; have := hX hx; simp at this; subst this; exact .eq c
  | andPos _ _ hX ih₁ ih₂ =>
    intro x hx
    rcases hX hx with h | h
    · exact .andL (ih₁ x h)
    · exact .andR (ih₂ x h)
  | andNeg _ _ ih₁ ih₂ => intro x hx; exact .andNeg (ih₁ x hx) (ih₂ x hx)
  | neg _ ih => intro x hx; exact .neg (ih x hx)

theorem Pol.flip_flip : ∀ p : Pol, p.flip.flip = p
  | .pos => rfl
  | .neg => rfl

/-- Guardedness gives Figure 4 derivations. -/
theorem Grd.gx {m : Set Voc.ℰ} : ∀ (Φ : Formula Voc) (p : Pol) (X : Set Voc.𝕍),
    (∀ x ∈ X, Grd m x p Φ) → ∃ π φ, GX m p X Φ π φ := by
  intro Φ
  induction Φ with
  | top =>
    intro p X h
    by_cases hX : X = ∅
    · subst hX; exact ⟨_, _, .none p _⟩
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hX
    cases p with
    | pos => cases h x hx
    | neg => exact ⟨_, _, .vac X⟩
  | pred e ts =>
    intro p X h
    by_cases hX : X = ∅
    · subst hX; exact ⟨_, _, .none p _⟩
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hX
    cases p with
    | pos =>
      have he : e ∈ m := by cases h x hx; assumption
      exact ⟨_, _, .pred X e ts he fun y hy => by cases h y hy; assumption⟩
    | neg => cases h x hx
  | eq y c =>
    intro p X h
    by_cases hX : X = ∅
    · subst hX; exact ⟨_, _, .none p _⟩
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hX
    cases p with
    | pos =>
      exact ⟨_, _, .eq X y c fun z hz => by cases h z hz; rfl⟩
    | neg => cases h x hx
  | neg φ ih =>
    intro p X h
    obtain ⟨π, φ', hg⟩ := ih p.flip X fun x hx => by cases h x hx; assumption
    exact ⟨π, _, .neg hg⟩
  | and φ ψ ih₁ ih₂ =>
    intro p X h
    cases p with
    | pos =>
      obtain ⟨π₁, φ₁, h₁⟩ := ih₁ .pos {x | x ∈ X ∧ Grd m x .pos φ} fun x hx => hx.2
      obtain ⟨π₂, φ₂, h₂⟩ := ih₂ .pos {x | x ∈ X ∧ Grd m x .pos ψ} fun x hx => hx.2
      refine ⟨_, _, .andPos h₁ h₂ fun x hx => ?_⟩
      cases h x hx with
      | andL h' => exact Or.inl ⟨hx, h'⟩
      | andR h' => exact Or.inr ⟨hx, h'⟩
    | neg =>
      obtain ⟨π₁, φ₁, h₁⟩ := ih₁ .neg X fun x hx => by cases h x hx; assumption
      obtain ⟨π₂, φ₂, h₂⟩ := ih₂ .neg X fun x hx => by cases h x hx; assumption
      exact ⟨_, _, .andNeg h₁ h₂⟩
  | ex _ _ _ | next _ _ _ | prev _ _ _ | eventually _ _ _ | since _ _ _ _ _ | letin _ _ _ _ _ _
  | agg _ _ _ _ _ _ =>
    intro p X h
    by_cases hX : X = ∅
    · subst hX; exact ⟨_, _, .none p _⟩
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hX
    cases h x hx

theorem gx_iff_grd {m : Set Voc.ℰ} {p : Pol} {X : Set Voc.𝕍} {Φ : Formula Voc} :
    (∃ π φ, GX m p X Φ π φ) ↔ ∀ x ∈ X, Grd m x p Φ :=
  ⟨fun ⟨_, _, h⟩ => h.grd, Grd.gx Φ p X⟩

theorem ACtx.m_toCaps_eq {Ξ : RwSetting Voc} {Γ : ACtx Voc} : Γ.m Ξ = Ξ.base ∪ {p | Cap.G ∈ Γ p} := rfl

/-- **Lemma A.1(1)**: `m_Γ ⊢ (π, ψ) ⇝^p_x (π', ψ')` for some `(π', ψ')` iff
    every `κ ∈ π` binds `x` or `Γ ⊢ ψ : GRD(x)^p`. -/
theorem lemma_A_1_1 (Ξ : RwSetting Voc) (Γ : ACtx Voc) (p : Pol) (x : Voc.𝕍) (π : GDisj Voc)
    (ψ : Formula Voc) :
    (∃ π' ψ', TGX (Γ.m Ξ) p x π ψ π' ψ') ↔ (∀ κ ∈ π, κ.Binds x) ∨ Γ.Grd Ξ x p ψ := by
  constructor
  · rintro ⟨π', ψ', h⟩
    cases h with
    | bound h => exact Or.inl h
    | filter h => exact Or.inr (h.grd x rfl)
  · rintro (h | h)
    · exact ⟨_, _, .bound h⟩
    · obtain ⟨π₀, ψ', hg⟩ := Grd.gx ψ p {x} fun y hy => by rw [hy]; exact h
      exact ⟨_, _, .filter hg⟩

/-- Lemma A.1(1), "in particular": a guard for `x` can be extracted from a
    trigger iff the trigger guards `x`. -/
theorem lemma_A_1_1' (Ξ : RwSetting Voc) (Γ : ACtx Voc) (x : Voc.𝕍) (π : GDisj Voc)
    (ψ : Formula Voc) :
    (∃ π' ψ', TGX (Γ.m Ξ) .pos x π ψ π' ψ') ↔ Γ.TrigGuards Ξ π ψ x :=
  lemma_A_1_1 Ξ Γ .pos x π ψ

/-- **Lemma A.1(2)**: `Guards^{m_Γ}_X(Φ) ≠ ⊥` iff `Γ ⊢ Φ : 𝔾⁺_X`. -/
theorem lemma_A_1_2 (Ξ : RwSetting Voc) (Γ : ACtx Voc) (X : Set Voc.𝕍) (Φ : Formula Voc) :
    Guards (Γ.m Ξ) X Φ ≠ none ↔ Γ.GSet Ξ .pos X Φ := by
  show _ ↔ ∀ x ∈ X, Grd (Γ.m Ξ) x .pos Φ
  rw [← gx_iff_grd]
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 h
    exact ⟨_, _, Guards_spec hr⟩
  · rintro ⟨π, φ, h⟩
    unfold Guards
    rw [dif_pos ⟨(π, φ), h⟩]; simp

theorem others_two_zero (φ ψ : Formula Voc) : othersConj [φ, ψ] ⟨0, by simp⟩ = ψ := rfl

theorem others_two_one (φ ψ : Formula Voc) : othersConj [φ, ψ] ⟨1, by simp⟩ = φ := rfl

/-- `And^𝕊_L` -/
theorem Typ.andSL {Ξ : RwSetting Voc} {Γ : ACtx Voc} {φ ψ : Formula Voc} {Δ : Set (EClause Voc)}
    (h : Typ Ξ Γ .S φ Δ) (hψ : ψ.Present) : Typ Ξ Γ .S (.and φ ψ) (ClauseSet.conj Δ ψ) := by
  have := Typ.andS [φ, ψ] ⟨0, by simp⟩ le_rfl h (fun i hi => by
    match i, hi with
    | ⟨1, _⟩, _ => exact hψ
    | ⟨0, _⟩, hi => exact absurd rfl hi)
  rwa [others_two_zero] at this

/-- `And^𝕊_R` -/
theorem Typ.andSR {Ξ : RwSetting Voc} {Γ : ACtx Voc} {φ ψ : Formula Voc} {Δ : Set (EClause Voc)}
    (h : Typ Ξ Γ .S ψ Δ) (hφ : φ.Present) : Typ Ξ Γ .S (.and φ ψ) (ClauseSet.conj Δ φ) := by
  have := Typ.andS [φ, ψ] ⟨1, by simp⟩ le_rfl h (fun i hi => by
    match i, hi with
    | ⟨0, _⟩, _ => exact hφ
    | ⟨1, _⟩, hi => exact absurd rfl hi)
  rwa [others_two_one] at this

/-! ## Figure 7 and Figure 5 -/

/-- The capabilities recorded by a context `(g, c, s)` of §4.4. -/
def toCaps (Γ : LetCtx Voc) : ACtx Voc := fun e =>
  match Γ e with
  | none => ∅
  | some (g, c, s) => {k | (k = .G ∧ g = true) ∨ (k = .C ∧ c = true) ∨ (k = .S ∧ s = true)}

theorem toCaps_G {Γ : LetCtx Voc} {e : Voc.ℰ} : Cap.G ∈ toCaps Γ e ↔ ∃ c s, Γ e = some (true, c, s) := by
  unfold toCaps; split <;> rename_i h
  · simp [h]
  · next g c s => simp [h]

theorem toCaps_C {Γ : LetCtx Voc} {e : Voc.ℰ} : Cap.C ∈ toCaps Γ e ↔ ∃ g s, Γ e = some (g, true, s) := by
  unfold toCaps; split <;> rename_i h
  · simp [h]
  · next g c s => simp [h]

theorem toCaps_S {Γ : LetCtx Voc} {e : Voc.ℰ} : Cap.S ∈ toCaps Γ e ↔ ∃ g c, Γ e = some (g, c, true) := by
  unfold toCaps; split <;> rename_i h
  · simp [h]
  · next g c s => simp [h]

theorem m_toCaps (Ξ : RwSetting Voc) (Γ : LetCtx Voc) : (toCaps Γ).m Ξ = Ξ.m Γ := by
  ext p; simp only [ACtx.m, RwSetting.m, Set.mem_union, Set.mem_setOf_eq, toCaps_G]

theorem CSet.map_subsingleton {𝒞 : CSet Voc} (h : 𝒞.Subsingleton)
    (f : GDisj Voc → Formula Voc → Effect Voc → EClause Voc) : (𝒞.map f).Subsingleton := by
  rintro _ ⟨C₁, h₁, rfl⟩ _ ⟨C₂, h₂, rfl⟩; rw [h h₁ h₂]

theorem bigTensor_subsingleton : ∀ {𝒞s : List (CSet Voc)}, (∀ 𝒞 ∈ 𝒞s, 𝒞.Subsingleton) →
    (CSet.bigTensor 𝒞s).Subsingleton
  | [], _ => Set.subsingleton_singleton
  | 𝒞 :: 𝒞s, h => by
    rintro _ ⟨C₁, h₁, D₁, k₁, rfl⟩ _ ⟨C₂, h₂, D₂, k₂, rfl⟩
    rw [h 𝒞 (by simp) h₁ h₂, bigTensor_subsingleton (fun 𝒞' h' => h 𝒞' (by simp [h'])) k₁ k₂]

/-- A derivation of Figure 5 yields at most one clause set. -/
theorem Rw.subsingleton {Ξ : RwSetting Voc} {Γ : LetCtx Voc} {α : Mode} {φ : Formula Voc}
    {𝒞 : CSet Voc} (h : Rw Ξ Γ α φ 𝒞) : 𝒞.Subsingleton := by
  refine Rw.rec (motive_1 := fun _ _ 𝒞 _ => 𝒞.Subsingleton)
    (motive_2 := fun _ 𝒞s _ => ∀ 𝒞 ∈ 𝒞s, 𝒞.Subsingleton) ?top ?evC ?evS ?letC ?letS ?neg
    ?andS ?andC ?exC ?exS ?futEv ?futNext ?futNextN (by simp)
    (fun _ _ ih ihs => by
      intro 𝒞 h𝒞; rcases List.mem_cons.1 h𝒞 with rfl | h𝒞
      · exact ih
      · exact ihs 𝒞 h𝒞) h
  case top => exact Set.subsingleton_singleton
  case evC => intros; exact Set.subsingleton_singleton
  case evS => intros; exact Set.subsingleton_singleton
  case letC => intros; exact Set.subsingleton_singleton
  case letS => intros; exact Set.subsingleton_singleton
  case neg => intro _ _ _ _ ih; exact ih
  case andS => intro _ _ _ _ _ _ ih; exact CSet.map_subsingleton ih _
  case andC => intro _ _ _ _ ih; exact bigTensor_subsingleton ih
  case exC => intro _ _ _ _ _ ih; exact CSet.map_subsingleton ih _
  case exS =>
    intro _ _ _ _ ih
    rintro _ ⟨C₁, h₁, -, rfl⟩ _ ⟨C₂, h₂, -, rfl⟩; rw [ih h₁ h₂]
  case futEv =>
    intro _ _ _ _ _ _ _ ih
    exact CSet.map_subsingleton (ih.anti fun _ h => h.1) _
  case futNext =>
    intro _ _ _ _ _ ih
    exact CSet.map_subsingleton (ih.anti fun _ h => h.1) _
  case futNextN =>
    intro _ _ _ _ _ ih
    exact CSet.map_subsingleton (ih.anti fun _ h => h.1) _

theorem typ_bigAnd {Ξ : RwSetting Voc} {Γ : LetCtx Voc} :
    ∀ {φs : List (Formula Voc)} {𝒞s : List (CSet Voc)},
      List.Forall₂ (fun φ 𝒞 => ∀ Δ ∈ 𝒞, Typ Ξ (toCaps Γ) .C φ Δ) φs 𝒞s → φs ≠ [] →
      ∀ Δ ∈ CSet.bigTensor 𝒞s, Typ Ξ (toCaps Γ) .C (bigAnd φs) Δ
  | [], _, .nil, h, _, _ => absurd rfl h
  | [φ], [𝒞], .cons h .nil, _, Δ, hΔ => by
    obtain ⟨C₁, h₁, C₂, h₂, rfl⟩ := hΔ
    simp only [CSet.bigTensor, Set.mem_singleton_iff] at h₂; subst h₂
    rw [Set.union_empty]; exact h C₁ h₁
  | φ :: ψ :: φs, 𝒞 :: 𝒞s, .cons h hs, _, Δ, hΔ => by
    obtain ⟨C₁, h₁, C₂, h₂, rfl⟩ := hΔ
    exact .andC (h C₁ h₁) (typ_bigAnd hs (by simp) C₂ h₂)

/-- Figure 5 derivations give Figure 7 derivations. -/
theorem typ_of_rw {Ξ : RwSetting Voc} {Γ : LetCtx Voc} {α : Mode} {φ : Formula Voc}
    {𝒞 : CSet Voc} (h : Rw Ξ Γ α φ 𝒞) : ∀ Δ ∈ 𝒞, Typ Ξ (toCaps Γ) α φ Δ := by
  refine Rw.rec (motive_1 := fun α φ 𝒞 _ => ∀ Δ ∈ 𝒞, Typ Ξ (toCaps Γ) α φ Δ)
    (motive_2 := fun φs 𝒞s _ => List.Forall₂ (fun φ 𝒞 => ∀ Δ ∈ 𝒞, Typ Ξ (toCaps Γ) .C φ Δ) φs 𝒞s)
    ?top ?evC ?evS ?letC ?letS ?neg
    ?andS ?andC ?exC ?exS ?futEv ?futNext ?futNextN .nil (fun _ _ ih ihs => .cons ih ihs) h
  case top => intro Δ hΔ; rw [Set.mem_singleton_iff] at hΔ; subst hΔ; exact .top
  case evC => intro e ts he Δ hΔ; rw [Set.mem_singleton_iff] at hΔ; subst hΔ; exact .evC e ts he
  case evS => intro e ts he Δ hΔ; rw [Set.mem_singleton_iff] at hΔ; subst hΔ; exact .evS e ts he
  case letC =>
    intro e ts he Δ hΔ; rw [Set.mem_singleton_iff] at hΔ; subst hΔ; exact .letC e ts (toCaps_C.2 he)
  case letS =>
    intro e ts he Δ hΔ; rw [Set.mem_singleton_iff] at hΔ; subst hΔ; exact .letS e ts (toCaps_S.2 he)
  case neg =>
    intro α φ 𝒞 _ ih Δ hΔ
    cases α with
    | C => exact .negC (ih Δ hΔ)
    | S => exact .negS (ih Δ hΔ)
  case andS =>
    intro φs j 𝒞 h2 _ hp ih Δ hΔ
    obtain ⟨C, hC, rfl⟩ := hΔ
    exact .andS φs j h2 (ih C hC) hp
  case andC =>
    intro φs 𝒞s h2 _ ih Δ hΔ
    exact typ_bigAnd ih (by intro h; rw [h] at h2; simp at h2) Δ hΔ
  case exC =>
    intro x φ 𝒞 _ hs ih Δ hΔ
    obtain ⟨C, hC, rfl⟩ := hΔ
    exact .exC x (ih C hC) (hs C hC)
  case exS =>
    intro x φ 𝒞 _ ih Δ hΔ
    obtain ⟨C, hC, hg, rfl⟩ := hΔ
    have := Typ.exS (Γ := toCaps Γ) x (ih C hC) fun c hc =>
      (lemma_A_1_1' Ξ (toCaps Γ) x c.π c.ψ).1 (by rw [m_toCaps]; exact hg c hc)
    rwa [m_toCaps] at this
  case futEv =>
    intro a b hab φ 𝒞 _ hb ih Δ hΔ
    obtain ⟨C, ⟨hC, hne, hun⟩, rfl⟩ := hΔ
    exact .futEv a b hab (ih C hC) hne hun hb
  case futNext =>
    intro b φ 𝒞 _ hb ih Δ hΔ
    obtain ⟨C, ⟨hC, hne, hun⟩, rfl⟩ := hΔ
    exact .futNext b (ih C hC) hne hun hb
  case futNextN =>
    intro n φ 𝒞 _ hn ih Δ hΔ
    obtain ⟨C, ⟨hC, hun⟩, rfl⟩ := hΔ
    exact .futNextN n (ih C hC) hun hn

/-- Figure 7 derivations give Figure 5 derivations. -/
theorem rw_of_typ {Ξ : RwSetting Voc} {Γ : LetCtx Voc} {α : Mode} {φ : Formula Voc}
    {Δ : Set (EClause Voc)} (h : Typ Ξ (toCaps Γ) α φ Δ) : ∃ 𝒞, Rw Ξ Γ α φ 𝒞 ∧ Δ ∈ 𝒞 := by
  induction h with
  | top => exact ⟨_, .top, rfl⟩
  | evC e ts he => exact ⟨_, .evC e ts he, rfl⟩
  | evS e ts he => exact ⟨_, .evS e ts he, rfl⟩
  | letC e ts he => exact ⟨_, .letC e ts (toCaps_C.1 he), rfl⟩
  | letS e ts he => exact ⟨_, .letS e ts (toCaps_S.1 he), rfl⟩
  | negC _ ih => obtain ⟨𝒞, h, hΔ⟩ := ih; exact ⟨𝒞, .neg (α := .C) h, hΔ⟩
  | negS _ ih => obtain ⟨𝒞, h, hΔ⟩ := ih; exact ⟨𝒞, .neg (α := .S) h, hΔ⟩
  | @andC φ ψ Δ₁ Δ₂ _ _ ih₁ ih₂ =>
    obtain ⟨𝒞₁, h₁, m₁⟩ := ih₁
    obtain ⟨𝒞₂, h₂, m₂⟩ := ih₂
    refine ⟨_, Rw.andC [φ, ψ] [𝒞₁, 𝒞₂] le_rfl (.cons h₁ (.cons h₂ .nil)), Δ₁, m₁, Δ₂ ∪ ∅,
      ⟨Δ₂, m₂, ∅, rfl, rfl⟩, by rw [Set.union_empty]⟩
  | andS φs j h2 _ hp ih =>
    obtain ⟨𝒞, h, hΔ⟩ := ih
    exact ⟨_, .andS φs j h2 h hp, _, hΔ, rfl⟩
  | @exC x φ Δ _ hs ih =>
    obtain ⟨𝒞, h, hΔ⟩ := ih
    refine ⟨_, .exC x h fun C hC => ?_, _, hΔ, rfl⟩
    rw [h.subsingleton hC hΔ]; exact hs
  | @exS x φ Δ _ hg ih =>
    obtain ⟨𝒞, h, hΔ⟩ := ih
    refine ⟨_, .exS x h, Δ, hΔ, fun c hc => ?_, ?_⟩
    · have := (lemma_A_1_1' Ξ (toCaps Γ) x c.π c.ψ).2 (hg c hc)
      rwa [m_toCaps] at this
    · simp only [ClauseSet.down, m_toCaps]
  | futEv a b hab _ hne hun hb ih =>
    obtain ⟨𝒞, h, hΔ⟩ := ih
    exact ⟨_, .futEv a b hab h hb, _, ⟨hΔ, hne, hun⟩, rfl⟩
  | futNext b _ hne hun hb ih =>
    obtain ⟨𝒞, h, hΔ⟩ := ih
    exact ⟨_, .futNext b h hb, _, ⟨hΔ, hne, hun⟩, rfl⟩
  | futNextN n _ hun hn ih =>
    obtain ⟨𝒞, h, hΔ⟩ := ih
    exact ⟨_, .futNextN n h hn, _, ⟨hΔ, hun⟩, rfl⟩

/-- **Figures 5 and 7 agree** (proof of Theorem A.2): `Γ ⊢ φ : α ▷ Δ` iff
    `Γ ⊢ φ ↪^α 𝒞` for some `𝒞 ∋ Δ`. -/
theorem typ_iff_rw (Ξ : RwSetting Voc) (Γ : LetCtx Voc) (α : Mode) (φ : Formula Voc)
    (Δ : Set (EClause Voc)) : Typ Ξ (toCaps Γ) α φ Δ ↔ ∃ 𝒞, Rw Ξ Γ α φ 𝒞 ∧ Δ ∈ 𝒞 :=
  ⟨rw_of_typ, fun ⟨_, h, hΔ⟩ => typ_of_rw h Δ hΔ⟩

theorem exs_strip : ∀ φ : Formula Voc, φ = Formula.exs (stripVars φ) (stripExists φ)
  | .ex x φ => by
    show Formula.ex x φ = Formula.ex x (Formula.exs (stripVars φ) (stripExists φ))
    rw [← exs_strip φ]
  | .top | .pred .. | .eq .. | .neg _ | .and .. | .next .. | .prev .. | .eventually .. | .since ..
  | .letin .. | .agg .. => rfl

/-! ### Inversions -/

theorem bigAnd_two_and : ∀ {φs : List (Formula Voc)}, 2 ≤ φs.length → ∃ φ ψ, bigAnd φs = .and φ ψ
  | [], h | [_], h => by simp at h
  | φ :: ψ :: φs, _ => ⟨φ, bigAnd (ψ :: φs), rfl⟩

theorem nextN_succ (n : ℕ) (φ : Formula Voc) : nextN (n + 1) φ = .next Interval.univ (nextN n φ) := by
  simp only [nextN, Function.iterate_succ_apply']

theorem nextN_next {n : ℕ} (hn : 1 ≤ n) (φ : Formula Voc) : ∃ I ψ, nextN n φ = .next I ψ := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  exact ⟨_, _, nextN_succ n φ⟩

theorem typ_S_neg {Ξ : RwSetting Voc} {Γ : ACtx Voc} {φ : Formula Voc} {Δ : Set (EClause Voc)}
    (h : Typ Ξ Γ .S (.neg φ) Δ) : Typ Ξ Γ .C φ Δ := by
  generalize hf : Formula.neg φ = f at h
  generalize hα : Mode.S = α at h
  cases h with
  | negS h => cases hf; exact h
  | andS φs j h2 =>
    obtain ⟨a, b, hab⟩ := bigAnd_two_and h2; rw [hab] at hf; cases hf
  | _ => (try cases hf) <;> (try cases hα)

theorem typ_C_neg {Ξ : RwSetting Voc} {Γ : ACtx Voc} {φ : Formula Voc} {Δ : Set (EClause Voc)}
    (h : Typ Ξ Γ .C (.neg φ) Δ) : Typ Ξ Γ .S φ Δ := by
  generalize hf : Formula.neg φ = f at h
  generalize hα : Mode.C = α at h
  cases h with
  | negC h => cases hf; exact h
  | futNextN n _ _ hn =>
    obtain ⟨I, ψ, he⟩ := nextN_next hn _; rw [he] at hf; cases hf
  | _ => (try cases hf) <;> (try cases hα)

theorem typ_C_and {Ξ : RwSetting Voc} {Γ : ACtx Voc} {φ ψ : Formula Voc} {Δ : Set (EClause Voc)}
    (h : Typ Ξ Γ .C (.and φ ψ) Δ) : ∃ Δ₁ Δ₂, Typ Ξ Γ .C φ Δ₁ ∧ Typ Ξ Γ .C ψ Δ₂ := by
  generalize hf : Formula.and φ ψ = f at h
  generalize hα : Mode.C = α at h
  cases h with
  | andC h₁ h₂ => cases hf; exact ⟨_, _, h₁, h₂⟩
  | futNextN n _ _ hn =>
    obtain ⟨I, ψ, he⟩ := nextN_next hn _; rw [he] at hf; cases hf
  | _ => (try cases hf) <;> (try cases hα)

theorem typ_S_top {Ξ : RwSetting Voc} {Γ : ACtx Voc} {Δ : Set (EClause Voc)} :
    ¬ Typ Ξ Γ .S .top Δ := by
  intro h
  generalize hf : (Formula.top : Formula Voc) = f at h
  generalize hα : Mode.S = α at h
  cases h with
  | andS φs j h2 =>
    obtain ⟨a, b, hab⟩ := bigAnd_two_and h2; rw [hab] at hf; cases hf
  | _ => (try cases hf) <;> (try cases hα)

/-- Suppressing `φ_l ∨ φ_r` is suppressing both. -/
theorem typ_S_or {Ξ : RwSetting Voc} {Γ : ACtx Voc} {φ ψ : Formula Voc} :
    (∃ Δ, Typ Ξ Γ .S (Formula.or φ ψ) Δ) ↔ (∃ Δ, Typ Ξ Γ .S φ Δ) ∧ ∃ Δ, Typ Ξ Γ .S ψ Δ := by
  constructor
  · rintro ⟨Δ, h⟩
    obtain ⟨Δ₁, Δ₂, h₁, h₂⟩ := typ_C_and (typ_S_neg h)
    exact ⟨⟨_, typ_C_neg h₁⟩, ⟨_, typ_C_neg h₂⟩⟩
  · rintro ⟨⟨Δ₁, h₁⟩, ⟨Δ₂, h₂⟩⟩
    exact ⟨_, .negS (.andC (.negC h₁) (.negC h₂))⟩

theorem gset_neg {Ξ : RwSetting Voc} {Γ : ACtx Voc} {p : Pol} {X : Set Voc.𝕍} {φ : Formula Voc} :
    Γ.GSet Ξ p X (.neg φ) ↔ Γ.GSet Ξ p.flip X φ := by
  constructor
  · intro h x hx; have := h x hx; cases this; assumption
  · intro h x hx; exact .neg (h x hx)

theorem CondOK.unique {Ξ : RwSetting Voc} {Γ' : ACtx Voc} {d : LetDef Voc} {caps caps' : Set Cap}
    (h : CondOK Ξ Γ' d caps) (h' : CondOK Ξ Γ' d caps') : caps = caps' := by
  have hG : Cap.G ∈ caps ↔ Cap.G ∈ caps' := h.1.trans h'.1.symm
  ext k
  cases k with
  | G => exact hG
  | C => rw [h.2.2.2.1, h'.2.2.2.1, hG]
  | S => rw [h.2.2.2.2, h'.2.2.2.2, hG]

/-! ### `TypeLet`, case by case -/

/-- `ret(𝒞^ℂ, 𝒞^𝕊)` of `TypeLet`. -/
noncomputable def retT (T : Typed Voc) (p : Voc.ℰ) (CC CS : CSet Voc) : Typed Voc :=
  ⟨Function.update T.Γ p (some (true, decide (CC ≠ ∅), decide (CS ≠ ∅))),
    Function.update T.CC p CC, Function.update T.CS p CS⟩

section cases
variable {Ξ : RwSetting Voc} {T : Typed Voc} {p : Voc.ℰ} {xs : List Voc.𝕍} {ψ : Formula Voc}

theorem typeLet_eq_once {I : Interval} {φ : Formula Voc} (hχ : stripExists ψ = .since I .top φ) :
    TypeLet Ξ T p xs ψ = if Guards (Ξ.m T.Γ) φ.fv φ = none then none
      else some (retT T p (if 0 ∈ I then gate (Ξ.cauN p) xs (RwAll Ξ T.Γ .C φ) else ∅) ∅) := by
  unfold TypeLet; rw [hχ]; rfl

theorem typeLet_eq_since {I : Interval} {φl φr : Formula Voc} (hχ : stripExists ψ = .since I φl φr)
    (hl : φl ≠ .top) :
    TypeLet Ξ T p xs ψ =
      if Guards (Ξ.m T.Γ) ({x | x ∈ xs} ∪ (Formula.since I φl φr).fv) (.neg φl) = none ∨
        Guards (Ξ.m T.Γ) ({x | x ∈ xs} ∪ (Formula.since I φl φr).fv) φr = none then none
      else if 0 ∈ I then
        some (retT T p (gate (Ξ.cauN p) xs (RwAll Ξ T.Γ .C φr))
          (gate (Ξ.supN p) xs ((RwAll Ξ T.Γ .S φl).tensor (RwAll Ξ T.Γ .S φr))))
      else some (retT T p ∅ (gate (Ξ.supN p) xs (RwAll Ξ T.Γ .S φl))) := by
  unfold TypeLet; rw [hχ]
  cases φl <;> first | exact absurd rfl hl | rfl

theorem typeLet_eq_prev {I : Interval} {φ : Formula Voc} (hχ : stripExists ψ = .prev I φ) :
    TypeLet Ξ T p xs ψ = if Guards (Ξ.m T.Γ) φ.fv φ = none then none else some (retT T p ∅ ∅) := by
  unfold TypeLet; rw [hχ]; rfl

theorem typeLet_eq_agg {ys : List Voc.𝕍} {ω : Voc.Ω} {ss : List (Term Voc)} {gs : List Voc.𝕍}
    {φ : Formula Voc} (hχ : stripExists ψ = .agg ys ω ss gs φ) :
    TypeLet Ξ T p xs ψ = if Guards (Ξ.m T.Γ) φ.fv φ = none then none else some (retT T p ∅ ∅) := by
  unfold TypeLet; rw [hχ]; rfl

/-- `χ` is not temporal and not an aggregation. -/
def Other (χ : Formula Voc) : Prop :=
  (∀ I φl φr, χ ≠ .since I φl φr) ∧ (∀ I φ, χ ≠ .prev I φ) ∧ (∀ ys ω ss gs φ, χ ≠ .agg ys ω ss gs φ)

theorem typeLet_eq_other {χ : Formula Voc} (hχ : stripExists ψ = χ) (ho : Other χ) :
    TypeLet Ξ T p xs ψ =
      if Guards (Ξ.m T.Γ) ({x | x ∈ xs} ∪ χ.fv) χ = none then
        some ⟨Function.update T.Γ p (some (false, false, false)), T.CC, T.CS⟩
      else if χ.Present then
        some (retT T p (gate (Ξ.cauN p) xs (RwAll Ξ T.Γ .C ψ)) (gate (Ξ.supN p) xs (RwAll Ξ T.Γ .S ψ)))
      else some (retT T p ∅ ∅) := by
  unfold TypeLet; rw [hχ]
  obtain ⟨h1, h2, h3⟩ := ho
  cases χ with
  | since I a b => exact absurd rfl (h1 I a b)
  | prev I a => exact absurd rfl (h2 I a)
  | agg ys ω ss gs a => exact absurd rfl (h3 ys ω ss gs a)
  | _ => rfl

end cases

theorem other_cases {χ : Formula Voc} (ho : Other χ) :
    gsOf xs ys χ = {x | x ∈ xs} ∪ {y | y ∈ ys} ∧ hatOf χ = χ ∧ ¬ TemporalOf χ ∧
      cauOf φ χ = (if χ.Present then some φ else none) ∧ supOf φ χ = (if χ.Present then some φ else none) := by
  obtain ⟨h1, h2, h3⟩ := ho
  cases χ with
  | since I a b => exact absurd rfl (h1 I a b)
  | prev I a => exact absurd rfl (h2 I a)
  | agg ys ω ss gs a => exact absurd rfl (h3 ys ω ss gs a)
  | _ => exact ⟨rfl, rfl, id, rfl, rfl⟩

theorem caps_retT (T : Typed Voc) (p : Voc.ℰ) (CC CS : CSet Voc) :
    (Cap.G ∈ toCaps (retT T p CC CS).Γ p) ∧ (Cap.C ∈ toCaps (retT T p CC CS).Γ p ↔ CC.Nonempty) ∧
      (Cap.S ∈ toCaps (retT T p CC CS).Γ p ↔ CS.Nonempty) := by
  simp only [retT, toCaps_G, toCaps_C, toCaps_S, Function.update_self, Option.some.injEq,
    Prod.mk.injEq]
  simp [Set.nonempty_iff_ne_empty]

theorem caps_filterOnly (T : Typed Voc) (p : Voc.ℰ) :
    Cap.G ∉ toCaps (Function.update T.Γ p (some (false, false, false))) p ∧
      Cap.C ∉ toCaps (Function.update T.Γ p (some (false, false, false))) p ∧
      Cap.S ∉ toCaps (Function.update T.Γ p (some (false, false, false))) p := by
  simp [toCaps_G, toCaps_C, toCaps_S]

theorem rwAll_nonempty (Ξ : RwSetting Voc) (Γ : LetCtx Voc) (α : Mode) (φ : Formula Voc) :
    (RwAll Ξ Γ α φ).Nonempty ↔ ∃ Δ, Typ Ξ (toCaps Γ) α φ Δ := by
  simp only [RwAll, typ_iff_rw]; exact ⟨fun ⟨Δ, 𝒞, h, hΔ⟩ => ⟨Δ, 𝒞, h, hΔ⟩, fun ⟨Δ, 𝒞, h, hΔ⟩ => ⟨Δ, 𝒞, h, hΔ⟩⟩

theorem tensor_nonempty {𝒞₁ 𝒞₂ : CSet Voc} : (𝒞₁.tensor 𝒞₂).Nonempty ↔ 𝒞₁.Nonempty ∧ 𝒞₂.Nonempty :=
  ⟨fun ⟨_, C₁, h₁, C₂, h₂, _⟩ => ⟨⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩, fun ⟨⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩ => ⟨_, C₁, h₁, C₂, h₂, rfl⟩⟩

theorem guards_ne_none (Ξ : RwSetting Voc) (Γ : LetCtx Voc) (X : Set Voc.𝕍) (Φ : Formula Voc) :
    Guards (Ξ.m Γ) X Φ ≠ none ↔ (toCaps Γ).GSet Ξ .pos X Φ := by
  rw [← m_toCaps]; exact lemma_A_1_2 Ξ (toCaps Γ) X Φ

theorem other_of {χ : Formula Voc} (h1 : ∀ I φl φr, χ ≠ .since I φl φr) (h2 : ∀ I φ, χ ≠ .prev I φ)
    (h3 : ∀ ys ω ss gs φ, χ ≠ .agg ys ω ss gs φ) : Other χ := ⟨h1, h2, h3⟩

theorem gx_X_other {d : LetDef Voc} (hfv : d.φ.fv = {x | x ∈ d.xs})
    (hys : ∀ y ∈ stripVars d.φ, y ∈ (stripExists d.φ).fv) :
    {x | x ∈ d.xs} ∪ (stripExists d.φ).fv = {x | x ∈ d.xs} ∪ {y | y ∈ stripVars d.φ} := by
  have he := exs_strip d.φ
  have hf : (stripExists d.φ).fv \ {y | y ∈ stripVars d.φ} = {x | x ∈ d.xs} := by
    rw [← fv_exs, ← he, hfv]
  ext x
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · by_cases hy : x ∈ stripVars d.φ
      · exact Or.inr hy
      · left; have : x ∈ (stripExists d.φ).fv \ {y | y ∈ stripVars d.φ} := ⟨h, hy⟩
        rw [hf] at this; exact this
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (hys x h)

theorem not_some_none {α : Type} {a : α} : ¬ (none : Option α) = some a := by simp

theorem typeLet_cond_other {Ξ : RwSetting Voc} {T T' : Typed Voc} {d : LetDef Voc} {χ : Formula Voc}
  (hfv : d.φ.fv = {x | x ∈ d.xs})
  (hX : {x | x ∈ d.xs} ∪ χ.fv = {x | x ∈ d.xs} ∪ {y | y ∈ stripVars d.φ})
  (h : TypeLet Ξ T d.e d.xs d.φ = some T') (hχ : stripExists d.φ = χ) (ho : Other χ) :
  (Cap.G ∈ toCaps T'.Γ d.e ↔ (toCaps T.Γ).GSet Ξ .pos (gsOf d.xs (stripVars d.φ) χ) (hatOf χ) ∧
    ∀ I φl φr, χ = .since I φl φr → (toCaps T.Γ).GSet Ξ .neg {x | x ∈ d.xs} φl) ∧
  (TemporalOf χ → Cap.G ∈ toCaps T'.Γ d.e) ∧
  (∀ ys ω ss gs φ, χ = .agg ys ω ss gs φ → Term.varsList ss ⊆ φ.fv) ∧
  (Cap.C ∈ toCaps T'.Γ d.e ↔ Cap.G ∈ toCaps T'.Γ d.e ∧ ∃ φc, cauOf d.φ χ = some φc ∧
    ∃ Δ, Typ Ξ (toCaps T.Γ) .C φc Δ) ∧
  (Cap.S ∈ toCaps T'.Γ d.e ↔ Cap.G ∈ toCaps T'.Γ d.e ∧ ∃ φs, supOf d.φ χ = some φs ∧
    ∃ Δ, Typ Ξ (toCaps T.Γ) .S φs Δ) := by
  have hG := guards_ne_none Ξ T.Γ
  have hR := rwAll_nonempty Ξ T.Γ
  obtain ⟨g1, g2, g3, g4, g5⟩ := other_cases (xs := d.xs) (ys := stripVars d.φ) (φ := d.φ) ho
  rw [typeLet_eq_other hχ ho, hX] at h
  rw [g1, g2, g4, g5]
  have hns : ∀ I φl φr, χ ≠ Formula.since I φl φr := ho.1
  split_ifs at h with hg hp <;> cases h
  · obtain ⟨cG, cC, cS⟩ := caps_filterOnly T d.e
    refine ⟨⟨fun h => absurd h cG, fun ⟨h, _⟩ => absurd hg ((hG _ _).2 h)⟩,
      fun h => absurd h g3, ?_, ⟨fun h => absurd h cC, fun ⟨h, _⟩ => absurd h cG⟩,
      ⟨fun h => absurd h cS, fun ⟨h, _⟩ => absurd h cG⟩⟩
    intro ys ω ss gs φ he; exact absurd he (ho.2.2 ys ω ss gs φ)
  · obtain ⟨cG, cC, cS⟩ := caps_retT T d.e (gate (Ξ.cauN d.e) d.xs (RwAll Ξ T.Γ .C d.φ))
      (gate (Ξ.supN d.e) d.xs (RwAll Ξ T.Γ .S d.φ))
    refine ⟨⟨fun _ => ⟨(hG _ _).1 hg, fun I a b he => absurd he (hns I a b)⟩, fun _ => cG⟩,
      fun h => absurd h g3, ?_, ?_, ?_⟩
    · intro ys ω ss gs φ he; exact absurd he (ho.2.2 ys ω ss gs φ)
    · rw [cC, if_pos hp, gate_nonempty, hR]
      exact ⟨fun h => ⟨cG, _, rfl, h⟩, fun ⟨_, _, he, h⟩ => by cases he; exact h⟩
    · rw [cS, if_pos hp, gate_nonempty, hR]
      exact ⟨fun h => ⟨cG, _, rfl, h⟩, fun ⟨_, _, he, h⟩ => by cases he; exact h⟩
  · obtain ⟨cG, cC, cS⟩ := caps_retT T d.e ∅ ∅
    refine ⟨⟨fun _ => ⟨(hG _ _).1 hg, fun I a b he => absurd he (hns I a b)⟩, fun _ => cG⟩,
      fun h => absurd h g3, ?_, ?_, ?_⟩
    · intro ys ω ss gs φ he; exact absurd he (ho.2.2 ys ω ss gs φ)
    · rw [cC, if_neg hp]
      exact ⟨fun h => absurd h Set.not_nonempty_empty, fun ⟨_, _, he, _⟩ => by simp at he⟩
    · rw [cS, if_neg hp]
      exact ⟨fun h => absurd h Set.not_nonempty_empty, fun ⟨_, _, he, _⟩ => by simp at he⟩


/-- **`TypeLet` computes the capabilities of Appendix A.** -/
theorem typeLet_cond {Ξ : RwSetting Voc} {T T' : Typed Voc} {d : LetDef Voc} (hb : d.φ.IsLetBody)
    (hfv : d.φ.fv = {x | x ∈ d.xs}) (hys : ∀ y ∈ stripVars d.φ, y ∈ (stripExists d.φ).fv)
    (hagg : ∀ ys ω ss gs φ, stripExists d.φ = .agg ys ω ss gs φ → Term.varsList ss ⊆ φ.fv)
    (h : TypeLet Ξ T d.e d.xs d.φ = some T') : CondOK Ξ (toCaps T.Γ) d (toCaps T'.Γ d.e) := by
  have hG := guards_ne_none Ξ T.Γ
  have hR := rwAll_nonempty Ξ T.Γ
  have hX := gx_X_other hfv hys
  unfold CondOK
  generalize hχ : stripExists d.φ = χ at hagg hX ⊢
  cases χ with
  | since I φl φr =>
    have hd := letBody_since hb hχ
    have hfv' : φl.fv ∪ φr.fv = {x | x ∈ d.xs} := by rw [hd] at hfv; exact hfv
    by_cases hl : φl = .top
    · subst hl
      rw [typeLet_eq_once hχ] at h
      by_cases hg : Guards (Ξ.m T.Γ) φr.fv φr = none
      · rw [if_pos hg] at h; cases h
      rw [if_neg hg] at h; cases h
      have hφfv : φr.fv = {x | x ∈ d.xs} := by simpa [Formula.fv] using hfv'
      have hgs := (hG _ _).1 hg
      have hCC : ((if 0 ∈ I then gate (Ξ.cauN d.e) d.xs (RwAll Ξ T.Γ .C φr) else ∅) : CSet Voc).Nonempty ↔
          ∃ φc, cauOf d.φ (Formula.since I .top φr) = some φc ∧ ∃ Δ, Typ Ξ (toCaps T.Γ) .C φc Δ := by
        simp only [cauOf]
        split_ifs with hI
        · rw [gate_nonempty, hR]
          exact ⟨fun h => ⟨_, rfl, h⟩, fun ⟨_, he, h⟩ => by cases he; exact h⟩
        · exact ⟨fun h => absurd h Set.not_nonempty_empty, fun ⟨_, he, _⟩ => by simp at he⟩
      generalize (if 0 ∈ I then gate (Ξ.cauN d.e) d.xs (RwAll Ξ T.Γ .C φr) else ∅) = CC at hCC ⊢
      obtain ⟨cG, cC, cS⟩ := caps_retT T d.e CC ∅
      refine ⟨⟨fun _ => ⟨?_, ?_⟩, fun _ => cG⟩, fun _ => cG, ?_, ?_, ?_⟩
      · simp only [gsOf, hatOf]; rw [← hφfv]; exact hgs
      · intro I' a b he; cases he; intro x _; exact Grd.vac
      · intro _ _ _ _ _ he; cases he
      · rw [cC, hCC]; exact ⟨fun h => ⟨cG, h⟩, fun h => h.2⟩
      · rw [cS]; simp only [supOf]
        split_ifs with hI
        · refine ⟨fun h => absurd h Set.not_nonempty_empty, fun ⟨_, _, he, hΔ⟩ => ?_⟩
          cases he
          obtain ⟨Δ, hΔ⟩ := (typ_S_or.1 hΔ).1
          exact absurd hΔ typ_S_top
        · refine ⟨fun h => absurd h Set.not_nonempty_empty, fun ⟨_, _, he, ⟨Δ, hΔ⟩⟩ => ?_⟩
          cases he; exact absurd hΔ typ_S_top
    · rw [typeLet_eq_since hχ hl] at h
      have hX' : {x | x ∈ d.xs} ∪ (Formula.since I φl φr).fv = {x | x ∈ d.xs} := by
        rw [show (Formula.since I φl φr).fv = φl.fv ∪ φr.fv from rfl, hfv', Set.union_self]
      rw [hX'] at h
      split_ifs at h with hg hI <;> cases h
      all_goals
        simp only [not_or] at hg
        have hgl := gset_neg.1 ((hG _ _).1 hg.1)
        have hgr := (hG _ _).1 hg.2
      · obtain ⟨cG, cC, cS⟩ := caps_retT T d.e (gate (Ξ.cauN d.e) d.xs (RwAll Ξ T.Γ .C φr))
          (gate (Ξ.supN d.e) d.xs ((RwAll Ξ T.Γ .S φl).tensor (RwAll Ξ T.Γ .S φr)))
        refine ⟨⟨fun _ => ⟨hgr, fun I' a b he => by cases he; exact hgl⟩, fun _ => cG⟩, fun _ => cG,
          ?_, ?_, ?_⟩
        · intro _ _ _ _ _ he; cases he
        · rw [cC]; simp only [cauOf, if_pos hI, gate_nonempty, hR]
          exact ⟨fun h => ⟨cG, _, rfl, h⟩, fun ⟨_, _, he, h⟩ => by cases he; exact h⟩
        · rw [cS]; simp only [supOf, if_pos hI, gate_nonempty, tensor_nonempty, hR]
          exact ⟨fun h => ⟨cG, _, rfl, typ_S_or.2 h⟩, fun ⟨_, _, he, h⟩ => by cases he; exact typ_S_or.1 h⟩
      · obtain ⟨cG, cC, cS⟩ := caps_retT T d.e ∅ (gate (Ξ.supN d.e) d.xs (RwAll Ξ T.Γ .S φl))
        refine ⟨⟨fun _ => ⟨hgr, fun I' a b he => by cases he; exact hgl⟩, fun _ => cG⟩, fun _ => cG,
          ?_, ?_, ?_⟩
        · intro _ _ _ _ _ he; cases he
        · rw [cC]; simp only [cauOf, if_neg hI]
          exact ⟨fun h => absurd h Set.not_nonempty_empty, fun ⟨_, _, he, _⟩ => by simp at he⟩
        · rw [cS]; simp only [supOf, if_neg hI, gate_nonempty, hR]
          exact ⟨fun h => ⟨cG, _, rfl, h⟩, fun ⟨_, _, he, h⟩ => by cases he; exact h⟩
  | prev I φ =>
    have hd := letBody_prev hb hχ
    have hφfv : φ.fv = {x | x ∈ d.xs} := by rw [hd] at hfv; exact hfv
    rw [typeLet_eq_prev hχ] at h
    split_ifs at h with hg; cases h
    obtain ⟨cG, cC, cS⟩ := caps_retT T d.e ∅ ∅
    refine ⟨⟨fun _ => ⟨?_, fun _ _ _ he => by cases he⟩, fun _ => cG⟩, fun _ => cG, ?_, ?_, ?_⟩
    · simp only [gsOf, hatOf]; rw [← hφfv]; exact (hG _ _).1 hg
    · intro _ _ _ _ _ he; cases he
    · rw [cC]; simp only [cauOf]
      exact ⟨fun h => absurd h Set.not_nonempty_empty, fun ⟨_, _, he, _⟩ => by simp at he⟩
    · rw [cS]; simp only [supOf]
      exact ⟨fun h => absurd h Set.not_nonempty_empty, fun ⟨_, _, he, _⟩ => by simp at he⟩
  | agg ys ω ss gs φ =>
    rw [typeLet_eq_agg hχ] at h
    split_ifs at h with hg; cases h
    obtain ⟨cG, cC, cS⟩ := caps_retT T d.e ∅ ∅
    refine ⟨⟨fun _ => ⟨(hG _ _).1 hg, fun _ _ _ he => by cases he⟩, fun _ => cG⟩, fun _ => cG,
      hagg, ?_, ?_⟩
    · rw [cC]; simp only [cauOf]
      exact ⟨fun h => absurd h Set.not_nonempty_empty, fun ⟨_, _, he, _⟩ => by simp at he⟩
    · rw [cS]; simp only [supOf]
      exact ⟨fun h => absurd h Set.not_nonempty_empty, fun ⟨_, _, he, _⟩ => by simp at he⟩
  | _ =>
    exact typeLet_cond_other hfv hX h hχ (other_of (fun _ _ _ he => by cases he)
      (fun _ _ he => by cases he) (fun _ _ _ _ _ he => by cases he))

/-- **`TypeLet` succeeds** when the let can be typed. -/
theorem typeLet_some {Ξ : RwSetting Voc} {T : Typed Voc} {d : LetDef Voc} {caps : Set Cap}
    (hb : d.φ.IsLetBody) (hfv : d.φ.fv = {x | x ∈ d.xs})
    (hc : CondOK Ξ (toCaps T.Γ) d caps) : ∃ T', TypeLet Ξ T d.e d.xs d.φ = some T' := by
  have hG := guards_ne_none Ξ T.Γ
  unfold CondOK at hc
  generalize hχ : stripExists d.φ = χ at hc
  obtain ⟨c1, c2, -, -, -⟩ := hc
  cases χ with
  | since I φl φr =>
    have hd := letBody_since hb hχ
    have hfv' : φl.fv ∪ φr.fv = {x | x ∈ d.xs} := by rw [hd] at hfv; exact hfv
    obtain ⟨g1, g2⟩ := c1.1 (c2 trivial)
    simp only [gsOf, hatOf] at g1
    by_cases hl : φl = .top
    · subst hl
      have hφfv : φr.fv = {x | x ∈ d.xs} := by simpa [Formula.fv] using hfv'
      rw [typeLet_eq_once hχ, if_neg ((hG _ _).2 (by rw [hφfv]; exact g1))]
      exact ⟨_, rfl⟩
    · rw [typeLet_eq_since hχ hl]
      have hX' : {x | x ∈ d.xs} ∪ (Formula.since I φl φr).fv = {x | x ∈ d.xs} := by
        rw [show (Formula.since I φl φr).fv = φl.fv ∪ φr.fv from rfl, hfv', Set.union_self]
      rw [hX', if_neg (by
        rw [not_or]
        exact ⟨(hG _ _).2 (gset_neg.2 (g2 I φl φr rfl)), (hG _ _).2 g1⟩)]
      split_ifs <;> exact ⟨_, rfl⟩
  | prev I φ =>
    have hd := letBody_prev hb hχ
    have hφfv : φ.fv = {x | x ∈ d.xs} := by rw [hd] at hfv; exact hfv
    obtain ⟨g1, -⟩ := c1.1 (c2 trivial)
    simp only [gsOf, hatOf] at g1
    rw [typeLet_eq_prev hχ, if_neg ((hG _ _).2 (by rw [hφfv]; exact g1))]
    exact ⟨_, rfl⟩
  | agg ys ω ss gs φ =>
    obtain ⟨g1, -⟩ := c1.1 (c2 trivial)
    simp only [gsOf, hatOf] at g1
    rw [typeLet_eq_agg hχ, if_neg ((hG _ _).2 g1)]
    exact ⟨_, rfl⟩
  | _ =>
    rw [typeLet_eq_other hχ (other_of (fun _ _ _ he => by cases he) (fun _ _ he => by cases he)
      (fun _ _ _ _ _ he => by cases he))]
    split_ifs <;> exact ⟨_, rfl⟩

theorem isLet_take_succ {ℒ : List (LetDef Voc)} {k : ℕ} (hk : k < ℒ.length) (e : Voc.ℰ) :
    IsLet (ℒ.take (k + 1)) e ↔ IsLet (ℒ.take k) e ∨ ℒ[k].e = e := by
  rw [List.take_succ_eq_append_getElem hk]
  simp only [IsLet, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨d, hd | rfl, he⟩
    · exact Or.inl ⟨d, hd, he⟩
    · exact Or.inr he
  · rintro (⟨d, hd, he⟩ | he)
    · exact ⟨d, Or.inl hd, he⟩
    · exact ⟨_, Or.inr rfl, he⟩

theorem toCaps_none : toCaps (Voc := Voc) (fun _ => none) = fun _ => ∅ := by
  funext e; simp [toCaps]

theorem mem_LetNames_take' {ℒ : List (LetDef Voc)} {k : ℕ} {e : Voc.ℰ} (h : IsLet (ℒ.take k) e) :
    ∃ m, ∃ hm : m < ℒ.length, m < k ∧ ℒ[m].e = e := by
  obtain ⟨d, hd, rfl⟩ := h
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hd
  rw [List.length_take] at hm
  exact ⟨m, by omega, by omega, by simp⟩

/-- **Theorem A.2**: `□φ` is in EF-MFOTL with clause set `Δ` iff the
    compilation of §4 succeeds on `□φ` with candidate clause set `Δ`: `TypeLet`
    accepts all lets and `Γ ⊢ χ ↪^ℂ 𝒞` with `Δ ∈ 𝒞`. -/
theorem theorem_A_2_aux (Ξ : RwSetting Voc) (L : LNF Voc) (hv : L.Valid) (hw : L.WFA)
    (Δ : Set (EClause Voc)) :
    EFMFOTL Ξ L Δ ↔
      ∃ T, TypeLets Ξ L.lets = some T ∧ ∃ 𝒞, Rw Ξ T.Γ .C (bigAnd L.chis) 𝒞 ∧ Δ ∈ 𝒞 := by
  have hb : ∀ d ∈ L.lets, d.φ.IsLetBody := hv.1
  obtain ⟨hnd, hwd⟩ := hw
  have hcond : ∀ k (hk : k < L.lets.length) {T T' : Typed Voc}, TypeLet Ξ T L.lets[k].e L.lets[k].xs L.lets[k].φ = some T' →
      CondOK Ξ (toCaps T.Γ) L.lets[k] (toCaps T'.Γ L.lets[k].e) := by
    intro k hk T T' h
    obtain ⟨h1, h2, h3⟩ := hwd _ (List.getElem_mem hk)
    exact typeLet_cond (hb _ (List.getElem_mem hk)) h1 h2 h3 h
  constructor
  · -- typable ⇒ compiles
    rintro ⟨Γ, ⟨h0, hk⟩, ht⟩
    have key : ∀ k ≤ L.lets.length, ∃ Tk, TypeLets Ξ (L.lets.take k) = some Tk ∧
        toCaps Tk.Γ = Γ.restrict {e | IsLet (L.lets.take k) e} := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨⟨fun _ => none, fun _ => ∅, fun _ => ∅⟩, by simp [TypeLets], ?_⟩
        rw [toCaps_none]; funext e
        simp [ACtx.restrict, IsLet]
      | succ k ih =>
        intro hk1
        obtain ⟨Tk, hTk, hcap⟩ := ih (by omega)
        have hc := hk k (by omega)
        rw [← hcap] at hc
        obtain ⟨T', hT'⟩ := typeLet_some (hb _ (List.getElem_mem (by omega)))
          (hwd _ (List.getElem_mem (by omega))).1 hc
        have hc' := hcond k (by omega) hT'
        have hu := hc'.unique hc
        refine ⟨T', by rw [TypeLets_take_succ k (by omega), hTk]; exact hT', ?_⟩
        funext e
        by_cases he : e = L.lets[k].e
        · subst he
          simp only [ACtx.restrict, Set.mem_setOf_eq,
            show IsLet (L.lets.take (k + 1)) L.lets[k].e from (isLet_take_succ (ℒ := L.lets) (k := k) (by omega) _).2 (Or.inr rfl),
            if_true]
          exact hu
        · have hf := (typeLet_frame hT').1 e he
          have : toCaps T'.Γ e = toCaps Tk.Γ e := by simp only [toCaps, hf.1]
          rw [this, hcap]
          have hiff : e ∈ {e | IsLet (L.lets.take k) e} ↔ e ∈ {e | IsLet (L.lets.take (k + 1)) e} := by
            simp only [Set.mem_setOf_eq, isLet_take_succ (ℒ := L.lets) (k := k) (by omega) e]
            exact ⟨Or.inl, fun h => h.resolve_right (fun h => he h.symm)⟩
          unfold ACtx.restrict
          by_cases hm : e ∈ {e | IsLet (L.lets.take k) e}
          · rw [if_pos hm, if_pos (hiff.1 hm)]
          · rw [if_neg hm, if_neg (fun h => hm (hiff.2 h))]
    obtain ⟨T, hT, hcap⟩ := key L.lets.length le_rfl
    rw [List.take_length] at hT hcap
    have hΓ : Γ = toCaps T.Γ := by
      rw [hcap]; funext e
      simp only [ACtx.restrict, Set.mem_setOf_eq]
      split_ifs with h
      · rfl
      · exact h0 e h
    rw [hΓ] at ht
    exact ⟨T, hT, rw_of_typ ht⟩
  · -- compiles ⇒ typable
    rintro ⟨T, hT, 𝒞, hr, hΔ⟩
    obtain ⟨hnl, -⟩ := typeLets_spec hb hnd hT
    refine ⟨toCaps T.Γ, ⟨fun e he => ?_, fun k hk => ?_⟩, typ_of_rw hr Δ hΔ⟩
    · simp only [toCaps, (hnl e he).1]
    · obtain ⟨Tk, hTk⟩ := TypeLets_take_isSome hT k hk.le
      obtain ⟨Tk1, hTk1⟩ := TypeLets_take_isSome hT (k + 1) hk
      have hlet : TypeLet Ξ Tk L.lets[k].e L.lets[k].xs L.lets[k].φ = some Tk1 := by
        rw [TypeLets_take_succ k hk, hTk] at hTk1; exact hTk1
      have hc := hcond k hk hlet
      have hTlen := TypeLets_take_len hT
      have hst : ∀ j (hj : j < k), T.Γ L.lets[j].e = Tk.Γ L.lets[j].e := by
        intro j hj
        obtain ⟨Tj1, hTj1⟩ := TypeLets_take_isSome hT (j + 1) (by omega)
        have a := (TypeLets_take_stable hnd j (by omega) L.lets.length (by omega) le_rfl Tj1 T hTj1 hTlen).1
        have b := (TypeLets_take_stable hnd j (by omega) k hj hk.le Tj1 Tk hTj1 hTk).1
        rw [a, b]
      have hres : toCaps Tk.Γ = (toCaps T.Γ).restrict {e | IsLet (L.lets.take k) e} := by
        funext e
        simp only [ACtx.restrict, Set.mem_setOf_eq]
        split_ifs with he
        · obtain ⟨m, hm, hmk, rfl⟩ := mem_LetNames_take' he
          simp only [toCaps, hst m hmk]
        · have := (TypeLets_take_fresh k hk.le Tk hTk e fun k' hk' h =>
            he ⟨(L.lets.take k)[k']'(by simp; omega), List.getElem_mem _, by rw [List.getElem_take]; exact h⟩).1
          simp only [toCaps, this]
      have hlast : toCaps Tk1.Γ L.lets[k].e = toCaps T.Γ L.lets[k].e := by
        have := (TypeLets_take_stable hnd k hk L.lets.length (by omega) le_rfl Tk1 T hTk1 hTlen).1
        simp only [toCaps, this]
      rw [hres, hlast] at hc
      exact hc

theorem figure7_AndS_binary : Figure7_AndS_binary Voc :=
  fun _ _ _ _ _ => ⟨Typ.andSL, Typ.andSR⟩

theorem lemma_A_1 : Lemma_A_1 Voc := ⟨lemma_A_1_1, lemma_A_1_1', lemma_A_1_2⟩

theorem theorem_A_2 : Theorem_A_2 Voc := fun Ξ L hv hw Δ => theorem_A_2_aux Ξ L hv hw Δ

end Paper
