/-
  The clauses of `R` have well-typed effects on non-let events, and are guarded.
-/
import Paper.Proof.Loop

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-- The effect is a well-typed event of a non-let name. -/
def EClause.EffTyped (ℒ : List (LetDef Voc)) (c : EClause Voc) : Prop :=
  c.ε.args.length = Voc.ι c.ε.name ∧ ¬ IsLet ℒ c.ε.name

theorem WellArity.mono {φ ψ : Formula Voc} (h : φ.WellArity) (hs : ψ.atoms ⊆ φ.atoms) :
    ψ.WellArity := fun a ha => h a (hs ha)

theorem atoms_bigAnd : ∀ φs : List (Formula Voc), (bigAnd φs).atoms = {a | ∃ φ ∈ φs, a ∈ φ.atoms}
  | [] => by simp [bigAnd, Formula.atoms]
  | [φ] => by simp [bigAnd]
  | φ :: ψ :: φs => by
    rw [show bigAnd (φ :: ψ :: φs) = .and φ (bigAnd (ψ :: φs)) from rfl]
    simp only [Formula.atoms, atoms_bigAnd (ψ :: φs)]
    ext x; simp

theorem atoms_nextN (φ : Formula Voc) : ∀ n, (nextN n φ).atoms = φ.atoms
  | 0 => rfl
  | n + 1 => by rw [nextN, Function.iterate_succ_apply']; simp only [Formula.atoms]; exact atoms_nextN φ n

/-- The statement of the typing invariant. -/
def TypedP (ℒ : List (LetDef Voc)) (φ : Formula Voc) (𝒞 : CSet Voc) : Prop :=
  φ.WellArity → ∀ C ∈ 𝒞, ∀ c ∈ C, c.EffTyped ℒ

theorem typed_rw {Ξ : RwSetting Voc} {Γ : LetCtx Voc} {ℒ : List (LetDef Voc)}
    (hΓ : ∀ e, (Γ e).isSome → IsLet ℒ e)
    (hlet : ∀ e, IsLet ℒ e → e ∉ Ξ.Cau ∧ e ∉ Ξ.Sup)
    (hobl : ∀ e, IsLet ℒ e → Voc.ι (Ξ.cauN e) = Voc.ι e ∧ Voc.ι (Ξ.supN e) = Voc.ι e ∧
      ¬ IsLet ℒ (Ξ.cauN e) ∧ ¬ IsLet ℒ (Ξ.supN e))
    {α : Mode} {φ : Formula Voc} {𝒞 : CSet Voc} (h : Rw Ξ Γ α φ 𝒞) : TypedP ℒ φ 𝒞 := by
  refine Rw.rec (motive_1 := fun _ φ 𝒞 _ => TypedP ℒ φ 𝒞)
    (motive_2 := fun φs 𝒞s _ => List.Forall₂ (TypedP ℒ) φs 𝒞s) ?top ?evC ?evS ?letC ?letS ?neg
    ?andS ?andC ?exC ?exS ?futEv ?futNext ?futNextN .nil (fun _ _ ih ihs => .cons ih ihs) h
  case top => intro _ C hC c hc; simp at hC; subst hC; simp at hc
  case evC =>
    intro e ts he hw C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    exact ⟨hw (e, ts) (by simp [Formula.atoms]), fun hl => (hlet e hl).1 he⟩
  case evS =>
    intro e ts he hw C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    exact ⟨hw (e, ts) (by simp [Formula.atoms]), fun hl => (hlet e hl).2 he⟩
  case letC =>
    intro e ts ⟨g, s, hg⟩ hw C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    have hl := hΓ e (by simp [hg])
    refine ⟨?_, (hobl e hl).2.2.1⟩
    simp only [Effect.args, Effect.name]; rw [(hobl e hl).1]; exact hw (e, ts) (by simp [Formula.atoms])
  case letS =>
    intro e ts ⟨g, c', hg⟩ hw C hC c hc
    simp at hC; subst hC; simp at hc; subst hc
    have hl := hΓ e (by simp [hg])
    refine ⟨?_, (hobl e hl).2.2.2⟩
    simp only [Effect.args, Effect.name]; rw [(hobl e hl).2.1]; exact hw (e, ts) (by simp [Formula.atoms])
  case neg => intro _ _ _ _ ih hw; exact ih hw
  case andS =>
    intro φs j 𝒞 _ _ _ ih hw C hC c hc
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    refine ih (WellArity.mono hw ?_) C₀ hC₀ c₀ hc₀
    rw [atoms_bigAnd]; intro a ha; exact ⟨_, List.getElem_mem _, ha⟩
  case andC =>
    intro φs 𝒞s _ _ ih hw C hC c hc
    obtain ⟨Cs, hCs, hsub⟩ := mem_bigTensor_eq hC
    obtain ⟨C', hC', hc'⟩ := hsub c hc
    have key : ∀ {φs : List (Formula Voc)} {𝒞s : List (CSet Voc)} {Cs : List (Set (EClause Voc))},
        List.Forall₂ (TypedP ℒ) φs 𝒞s → List.Forall₂ (· ∈ ·) Cs 𝒞s →
        ∀ C' ∈ Cs, ∃ φ ∈ φs, ∃ 𝒞, TypedP ℒ φ 𝒞 ∧ C' ∈ 𝒞 := by
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
    exact hg (WellArity.mono hw (by rw [atoms_bigAnd]; intro a ha; exact ⟨φ, hφ, ha⟩)) C' hm c hc'
  case exC =>
    intro x φ 𝒞 _ _ ih hw C hC c hc
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    obtain ⟨h1, h2⟩ := ih hw C₀ hC₀ c₀ hc₀
    refine ⟨?_, ?_⟩
    · simp only [Effect.subst_name, Effect.subst_args]
      rw [← h1]; clear h1 h2
      generalize c₀.ε.args = ts
      induction ts with
      | nil => rfl
      | cons t ts ih' => simp only [Term.substList, List.length_cons, ih']
    · simpa [Effect.subst_name] using h2
  case exS =>
    intro x φ 𝒞 _ ih hw C hC c' hc'
    obtain ⟨C₀, hC₀, -, rfl⟩ := hC
    obtain ⟨c, hc, -, hε⟩ := hc'
    rw [EClause.EffTyped, hε]; exact ih hw C₀ hC₀ c hc
  case futEv =>
    intro a b h φ 𝒞 _ _ ih hw C hC c' hc'
    obtain ⟨C₀, ⟨hC₀, -, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, -, -⟩ := hun c hc
    have := ih hw C₀ hC₀ c hc
    rw [EClause.EffTyped, hε] at this
    simpa [EClause.EffTyped, hε, deferEffect, Effect.args, Effect.name] using this
  case futNext =>
    intro b φ 𝒞 _ _ ih hw C hC c' hc'
    obtain ⟨C₀, ⟨hC₀, -, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, -, -⟩ := hun c hc
    have := ih hw C₀ hC₀ c hc
    rw [EClause.EffTyped, hε] at this
    simpa [EClause.EffTyped, hε, deferEffect, Effect.args, Effect.name] using this
  case futNextN =>
    intro n φ 𝒞 _ _ ih hw C hC c' hc'
    obtain ⟨C₀, ⟨hC₀, hun⟩, rfl⟩ := hC
    obtain ⟨c, hc, rfl⟩ := hc'
    obtain ⟨⟨p, ts, hε⟩, -, -⟩ := hun c hc
    have := ih (WellArity.mono hw (by rw [atoms_nextN])) C₀ hC₀ c hc
    rw [EClause.EffTyped, hε] at this
    simpa [EClause.EffTyped, hε, deferEffect, Effect.args, Effect.name] using this

end Paper
