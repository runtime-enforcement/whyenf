/-
  The hypotheses of Theorem 4.3, and what `Compile` produces.
-/
import Paper.Proof.Items

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-- The specification of a compiled rule. -/
inductive RuleSpec (c : EClause Voc) : Item Voc → Prop
  | cau (e : Voc.ℰ) (ts : List (Term Voc)) (trig : Clause Voc) :
      c.ε = .cau e ts → toClause c.π c.ψ = some trig → RuleSpec c (.rule none .plus e ts none none trig)
  | sup (e : Voc.ℰ) (ts : List (Term Voc)) (trig : Clause Voc) :
      c.ε = .sup e ts → toClause c.π c.ψ = some trig → RuleSpec c (.rule none .minus e ts none none trig)
  | ev (n : ℕ) (e : Voc.ℰ) (ts : List (Term Voc)) (trig : Clause Voc) :
      c.ε = .ev (Interval.icc n n le_rfl) e ts → toClause c.π c.ψ = some trig →
      RuleSpec c (.rule none .plus e ts (some n) none trig)
  | nexts (n : ℕ) (e : Voc.ℰ) (ts : List (Term Voc)) (trig : Clause Voc) :
      c.ε = .nexts n e ts → toClause c.π c.ψ = some trig →
      RuleSpec c (.rule none .plus e ts none (some n) trig)

theorem ruleItem_spec {c : EClause Voc} {it : Item Voc} (h : ruleItem c = some it) : RuleSpec c it := by
  unfold ruleItem at h
  simp only [bind, Option.bind_eq_some_iff] at h
  obtain ⟨trig, ht, h⟩ := h
  cases hε : c.ε with
  | cau e ts => rw [hε] at h; simp [pure] at h; subst h; exact .cau e ts trig hε ht
  | sup e ts => rw [hε] at h; simp [pure] at h; subst h; exact .sup e ts trig hε ht
  | ev I e ts =>
    rw [hε] at h; simp only at h
    split_ifs at h with hI
    simp [pure] at h; subst h
    have := hI.choose_spec
    rw [this] at hε
    exact .ev _ e ts trig hε ht
  | nexts n e ts => rw [hε] at h; simp [pure] at h; subst h; exact .nexts n e ts trig hε ht

theorem RuleSpec.isRule {c : EClause Voc} {it : Item Voc} (h : RuleSpec c it) : it.isRule := by
  cases h <;> rfl

theorem RuleSpec.defName {c : EClause Voc} {it : Item Voc} (h : RuleSpec c it) : it.defName? = none := by
  cases h <;> rfl

/-- The hypotheses of Theorem 4.3. -/
structure Setup (Voc : Vocabulary) extends FinalSetting Voc where
  mfotl : φ.IsMFOTL
  closed : φ.fv = ∅
  equiv : ∀ σ : Trace Voc.toSignature, σ.length = ⊤ → Admissible {e | IsLet L.lets e} σ →
    ((Formula.Always φ).satTr σ Val.empty 0 ↔ L.toFormula.satTr σ Val.empty 0)
  conflict : ConflictCheck L.lets R
  O : StabOrder Voc
  dfg : DFGCheck O L.lets R
  rk : Voc.ℰ → ℕ
  topo : TopoOrder L.lets R rk
  rs : List (EClause Voc)
  hrs : ∀ c, c ∈ rs ↔ c ∈ R
  evTys : Voc.ℰ → List Ty
  colTy : Voc.𝕍 → Ty
  P : Program Voc
  hP : Compile Ξ L.lets T.Γ rs rk evTys colTy = some P

namespace Setup
variable (U : Setup Voc)

/-- The sorted clauses. -/
def sorted : List (EClause Voc) :=
  U.rs.mergeSort fun c c' => decide (U.rk c.ε.name ≤ U.rk c'.ε.name)

theorem all_typed : ∀ d ∈ U.L.lets, (U.T.Γ d.e).isSome := by
  obtain ⟨-, h⟩ := typeLets_spec U.lets_body U.wf.nodup U.hT
  intro d hd
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  exact (h k hk).choose_spec.2.2.1

theorem compile_spec : ∃ (its : List (Item Voc)) (rules : List (EClause Voc × Item Voc)),
    List.Forall₂ (fun d it => LetItemSpec U.Ξ U.T.Γ U.colTy d it) U.L.lets its ∧
    List.Forall₂ (fun c p => p.1 = c ∧ RuleSpec c p.2) U.sorted rules ∧
    U.P.items = its ++ withSections U.rk none rules := by
  have h := U.hP
  unfold Compile at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨its, hits, rules, hrules, hP⟩ := h
  have hfilter : U.L.lets.filter (fun d => (U.T.Γ d.e).isSome) = U.L.lets :=
    List.filter_eq_self.2 fun d hd => U.all_typed d hd
  rw [hfilter] at hits
  refine ⟨its, rules, (mapM_forall₂ hits).imp fun d it h => letItem_spec _ _ _ _ h,
    (mapM_forall₂ hrules).imp fun c p h => ?_, by rw [← hP]⟩
  simp only [Functor.map, Option.map_eq_some_iff] at h
  obtain ⟨it, hit, rfl⟩ := h
  exact ⟨rfl, ruleItem_spec hit⟩

end Setup

end Paper
