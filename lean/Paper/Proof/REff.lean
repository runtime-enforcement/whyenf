/-
  The effects of the clauses of `R`: caused events are causable or obligation
  events, suppressed events are suppressable, and deferrals are by at least 1.
-/
import Paper.Proof.RProps

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-- The names caused by `P`. -/
def RwSetting.CauAll (Ξ : RwSetting Voc) : Set Voc.ℰ := Ξ.Cau ∪ Set.range Ξ.cauN ∪ Set.range Ξ.supN

/-- The shape of an effect. -/
def Effect.OK (Ξ : RwSetting Voc) : Effect Voc → Prop
  | .cau e _ => e ∈ Ξ.CauAll
  | .sup e _ => e ∈ Ξ.Sup
  | .ev J e _ => (∃ n, 1 ≤ n ∧ J = Interval.icc n n le_rfl) ∧ e ∈ Ξ.CauAll
  | .nexts n e _ => 1 ≤ n ∧ e ∈ Ξ.CauAll

theorem Effect.OK.subst {Ξ : RwSetting Voc} (d : Voc.𝔻) (x : Voc.𝕍) :
    ∀ {ε : Effect Voc}, ε.OK Ξ → (ε.subst d x).OK Ξ
  | .cau .., h | .sup .., h | .ev .., h | .nexts .., h => h

theorem okRw {Ξ : RwSetting Voc} {Γ : LetCtx Voc} {α : Mode} {φ : Formula Voc} {𝒞 : CSet Voc}
    (h : Rw Ξ Γ α φ 𝒞) : ∀ C ∈ 𝒞, ∀ c ∈ C, c.ε.OK Ξ := by
  refine Rw.rec (motive_1 := fun _ _ 𝒞 _ => ∀ C ∈ 𝒞, ∀ c ∈ C, c.ε.OK Ξ)
    (motive_2 := fun _ 𝒞s _ => ∀ 𝒞 ∈ 𝒞s, ∀ C ∈ 𝒞, ∀ c ∈ C, c.ε.OK Ξ) ?top ?evC ?evS ?letC ?letS ?neg
    ?andS ?andC ?exC ?exS ?futEv ?futNext ?futNextN (by simp)
    (fun _ _ ih ihs => by
      intro 𝒞 h𝒞; rcases List.mem_cons.1 h𝒞 with rfl | h𝒞
      · exact ih
      · exact ihs 𝒞 h𝒞) h
  case top => intro C hC c hc; simp at hC; subst hC; simp at hc
  case evC =>
    intro e ts he C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    exact Or.inl (Or.inl he)
  case evS =>
    intro e ts he C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    exact he
  case letC =>
    intro e ts _ C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    exact Or.inl (Or.inr ⟨e, rfl⟩)
  case letS =>
    intro e ts _ C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    exact Or.inr ⟨e, rfl⟩
  case neg => intro _ _ _ _ ih; exact ih
  case andS =>
    intro φs j 𝒞 _ _ _ ih C hC c hc
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    exact ih C₀ hC₀ c₀ hc₀
  case andC =>
    intro φs 𝒞s _ _ ih C hC c hc
    obtain ⟨Cs, hCs, hsub⟩ := mem_bigTensor_eq hC
    obtain ⟨C', hC', hc'⟩ := hsub c hc
    obtain ⟨𝒞, h𝒞, hm⟩ := forall₂_mem_left hCs C' hC'
    exact ih 𝒞 h𝒞 C' hm c hc'
  case exC =>
    intro x φ 𝒞 _ _ ih C hC c hc
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    exact (ih C₀ hC₀ c₀ hc₀).subst _ _
  case exS =>
    intro x φ 𝒞 _ ih C hC c' hc'
    obtain ⟨C₀, hC₀, -, rfl⟩ := hC
    obtain ⟨c, hc, -, hε⟩ := hc'
    rw [hε]; exact ih C₀ hC₀ c hc
  case futEv =>
    intro a b h φ 𝒞 _ hb ih C hC c' hc'
    obtain ⟨C₀, ⟨hC₀, -, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, -, -⟩ := hun c hc
    have := ih C₀ hC₀ c hc
    rw [hε] at this
    simp only [hε, deferEffect]
    exact ⟨⟨b, hb, rfl⟩, this⟩
  case futNext =>
    intro b φ 𝒞 _ _ ih C hC c' hc'
    obtain ⟨C₀, ⟨hC₀, -, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, -, -⟩ := hun c hc
    have := ih C₀ hC₀ c hc
    rw [hε] at this
    simp only [hε, deferEffect]
    exact ⟨le_rfl, this⟩
  case futNextN =>
    intro n φ 𝒞 _ hn ih C hC c' hc'
    obtain ⟨C₀, ⟨hC₀, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, -, -⟩ := hun c hc
    have := ih C₀ hC₀ c hc
    rw [hε] at this
    simp only [hε, deferEffect]
    exact ⟨hn, this⟩

/-- The terms `ts` evaluate whenever their variables are assigned. -/
def ArgsOK (ts : List (Term Voc)) : Prop :=
  ∀ v : Val Voc, v.Covers (Term.varsList ts) → (Term.evalList v ts).isSome

theorem ArgsOK.subst {ts : List (Term Voc)} (h : ArgsOK ts) (d : Voc.𝔻) (x : Voc.𝕍) :
    ArgsOK (Term.substList d x ts) := by
  intro v hv
  rw [Term.evalList_subst]
  refine h _ fun y hy => ?_
  by_cases hyx : y = x
  · subst hyx; simp [Val.upd]
  · rw [Val.upd_ne _ _ hyx]
    exact hv y (by rw [Term.varsList_subst]; exact ⟨hy, hyx⟩)

theorem FunOK.mono {φ ψ : Formula Voc} (h : φ.FunOK) (hs : ψ.atoms ⊆ φ.atoms) : ψ.FunOK :=
  fun a ha => h a (hs ha)

/-- The statement of the evaluation invariant. -/
def ArgsP (φ : Formula Voc) (𝒞 : CSet Voc) : Prop :=
  φ.FunOK → ∀ C ∈ 𝒞, ∀ c ∈ C, ArgsOK c.ε.args

theorem args_rw {Ξ : RwSetting Voc} {Γ : LetCtx Voc} {α : Mode} {φ : Formula Voc} {𝒞 : CSet Voc}
    (h : Rw Ξ Γ α φ 𝒞) : ArgsP φ 𝒞 := by
  refine Rw.rec (motive_1 := fun _ φ 𝒞 _ => ArgsP φ 𝒞)
    (motive_2 := fun φs 𝒞s _ => List.Forall₂ ArgsP φs 𝒞s) ?top ?evC ?evS ?letC ?letS ?neg
    ?andS ?andC ?exC ?exS ?futEv ?futNext ?futNextN .nil (fun _ _ ih ihs => .cons ih ihs) h
  case top => intro _ C hC c hc; simp at hC; subst hC; simp at hc
  case evC =>
    intro e ts _ hw C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    exact hw (e, ts) (by simp [Formula.atoms])
  case evS =>
    intro e ts _ hw C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    exact hw (e, ts) (by simp [Formula.atoms])
  case letC =>
    intro e ts _ hw C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    exact hw (e, ts) (by simp [Formula.atoms])
  case letS =>
    intro e ts _ hw C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    exact hw (e, ts) (by simp [Formula.atoms])
  case neg => intro _ _ _ _ ih hw; exact ih hw
  case andS =>
    intro φs j 𝒞 _ _ _ ih hw C hC c hc
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    refine ih (FunOK.mono hw ?_) C₀ hC₀ c₀ hc₀
    rw [atoms_bigAnd]; intro a ha; exact ⟨_, List.getElem_mem _, ha⟩
  case andC =>
    intro φs 𝒞s _ _ ih hw C hC c hc
    obtain ⟨Cs, hCs, hsub⟩ := mem_bigTensor_eq hC
    obtain ⟨C', hC', hc'⟩ := hsub c hc
    have key : ∀ {φs : List (Formula Voc)} {𝒞s : List (CSet Voc)} {Cs : List (Set (EClause Voc))},
        List.Forall₂ ArgsP φs 𝒞s → List.Forall₂ (· ∈ ·) Cs 𝒞s →
        ∀ C' ∈ Cs, ∃ φ ∈ φs, ∃ 𝒞, ArgsP φ 𝒞 ∧ C' ∈ 𝒞 := by
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
    exact hg (FunOK.mono hw (by rw [atoms_bigAnd]; intro a ha; exact ⟨φ, hφ, ha⟩)) C' hm c hc'
  case exC =>
    intro x φ 𝒞 _ _ ih hw C hC c hc
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    simp only [Effect.subst_args]
    exact (ih hw C₀ hC₀ c₀ hc₀).subst _ _
  case exS =>
    intro x φ 𝒞 _ ih hw C hC c' hc'
    obtain ⟨C₀, hC₀, -, rfl⟩ := hC
    obtain ⟨c, hc, -, hε⟩ := hc'
    rw [hε]; exact ih hw C₀ hC₀ c hc
  case futEv =>
    intro a b h φ 𝒞 _ _ ih hw C hC c' hc'
    obtain ⟨C₀, ⟨hC₀, -, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, -, -⟩ := hun c hc
    have := ih hw C₀ hC₀ c hc
    rw [hε] at this
    simpa [hε, deferEffect, Effect.args] using this
  case futNext =>
    intro b φ 𝒞 _ _ ih hw C hC c' hc'
    obtain ⟨C₀, ⟨hC₀, -, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, -, -⟩ := hun c hc
    have := ih hw C₀ hC₀ c hc
    rw [hε] at this
    simpa [hε, deferEffect, Effect.args] using this
  case futNextN =>
    intro n φ 𝒞 _ _ ih hw C hC c' hc'
    obtain ⟨C₀, ⟨hC₀, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, -, -⟩ := hun c hc
    have := ih (FunOK.mono hw (by rw [atoms_nextN])) C₀ hC₀ c hc
    rw [hε] at this
    simpa [hε, deferEffect, Effect.args] using this

namespace Setup
variable (U : Setup Voc)

/-- **Every clause of `R`** has an effect of the right shape. -/
theorem R_ok : ∀ c ∈ U.R, c.ε.OK U.Ξ := by
  obtain ⟨hRC, -, -, hcases⟩ := realization_structure U.hR
  obtain ⟨hnl, hspec⟩ := typeLets_spec U.lets_body U.wf.nodup U.hT
  intro c hc
  rcases hcases c hc with hc | ⟨p, f, hf, hcf⟩ | ⟨p, g, hg, hcg⟩
  · exact okRw U.hrw U.C U.hC c hc
  · by_cases hp : IsLet U.L.lets p
    · obtain ⟨d, hd, rfl⟩ := hp
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
      obtain ⟨Tk, -, hTk, -, hCC, -⟩ := hspec k hk
      obtain ⟨body, 𝒞, C₀, hr, hC₀, rfl, -⟩ := hCC f hf
      obtain ⟨c₀, hc₀, rfl⟩ := hcf
      exact okRw hr C₀ hC₀ c₀ hc₀
    · rw [(hnl p hp).2.1] at hf; exact absurd hf (Set.notMem_empty _)
  · by_cases hp : IsLet U.L.lets p
    · obtain ⟨d, hd, rfl⟩ := hp
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
      obtain ⟨Tk, -, hTk, -, -, hCS⟩ := hspec k hk
      obtain ⟨bs, hbs, rfl, -⟩ := hCS g hg
      obtain ⟨c₀, ⟨b, hb, hc₀⟩, rfl⟩ := hcg
      obtain ⟨hr, hC, -⟩ := hbs b hb
      exact okRw hr b.2.2 hC c₀ hc₀
    · rw [(hnl p hp).2.2] at hg; exact absurd hg (Set.notMem_empty _)

/-- **The effect arguments of every clause of `R` evaluate.** -/
theorem R_args : ∀ c ∈ U.R, ArgsOK c.ε.args := by
  obtain ⟨hRC, -, -, hcases⟩ := realization_structure U.hR
  obtain ⟨hnl, hspec⟩ := typeLets_spec U.lets_body U.wf.nodup U.hT
  intro c hc
  rcases hcases c hc with hc | ⟨p, f, hf, hcf⟩ | ⟨p, g, hg, hcg⟩
  · refine args_rw U.hrw ?_ U.C U.hC c hc
    intro a ha; rw [atoms_bigAnd] at ha
    obtain ⟨χ, hχ, ha⟩ := ha; exact U.wf.fun_ok.2 χ hχ a ha
  · by_cases hp : IsLet U.L.lets p
    · obtain ⟨d, hd, rfl⟩ := hp
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
      obtain ⟨Tk, -, hTk, -, hCC, -⟩ := hspec k hk
      obtain ⟨body, 𝒞, C₀, hr, hC₀, rfl, hfvb, -, hat, -⟩ := hCC f hf
      obtain ⟨c₀, hc₀, rfl⟩ := hcf
      exact args_rw hr (FunOK.mono (U.wf.fun_ok.1 _ hd) hat) C₀ hC₀ c₀ hc₀
    · rw [(hnl p hp).2.1] at hf; exact absurd hf (Set.notMem_empty _)
  · by_cases hp : IsLet U.L.lets p
    · obtain ⟨d, hd, rfl⟩ := hp
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
      obtain ⟨Tk, -, hTk, -, -, hCS⟩ := hspec k hk
      obtain ⟨bs, hbs, rfl, -⟩ := hCS g hg
      obtain ⟨c₀, ⟨b, hb, hc₀⟩, rfl⟩ := hcg
      obtain ⟨hr, hC, hfvb, -, hat⟩ := hbs b hb
      exact args_rw hr (FunOK.mono (U.wf.fun_ok.1 _ hd) hat) b.2.2 hC c₀ hc₀
    · rw [(hnl p hp).2.2] at hg; exact absurd hg (Set.notMem_empty _)

end Setup

end Paper
