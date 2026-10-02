/-
  Algorithm 1 with the program `P`: the tables after a time-point stay finite.
-/
import Paper.Proof.Term
import Paper.Proof.REff

namespace Paper

open Classical

variable {Voc : Vocabulary}

namespace Setup
variable {U : Setup Voc}

namespace PtIn
variable (J : U.PtIn)

/-- **A trigger that holds yields a firing row.** -/
theorem sat_A {c : EClause Voc} (hc : c ∈ U.R) (x : Trip Voc) {w : Val Voc}
    (hw : w.Covers c.vars) (hs : c.trig.sat (J.St x) w J.H.length) {a : List Voc.𝔻}
    (ha : Term.evalList w c.ε.args = some a) : a ∈ J.A c x := by
  have hg := (U.R_props c hc).2
  simp only [EClause.trig, Formula.sat] at hs
  obtain ⟨hπ, hψ⟩ := hs
  obtain ⟨κ, hκ, hκs⟩ := (sat_disj _ _ _ _).1 hπ
  have hsub := hg κ hκ
  have hcov : w.Covers κ.toFormula.fv := fun y hy =>
    hw y (Or.inl (Or.inl (by rw [fv_gdisj]; exact ⟨κ, hκ, hy⟩)))
  have hag : ∀ y ∈ κ.toFormula.fv, w.restrict κ.toFormula.fv y = w y := Val.restrict_agree w _
  refine ⟨w.restrict κ.toFormula.fv, ?_, ?_⟩
  · have hψv : c.ψ.sat (J.St x) (w.restrict κ.toFormula.fv) J.H.length :=
      (Formula.sat_congr _ _ _ _ _ fun y hy => hag y (hsub (Or.inl hy))).2 hψ
    by_cases h0 : c.π = [[]]
    · rw [h0, trigSem_top]
      rw [h0] at hκ; simp only [List.mem_singleton] at hκ; subst hκ
      have hfv0 : GConj.toFormula ([] : GConj Voc) = .top := rfl
      refine ⟨?_, hψv⟩
      rw [Val.restrict_dom hcov, hfv0]
      have : c.ψ.fv ⊆ ∅ := fun y hy => by have := hsub (Or.inl hy); rwa [hfv0] at this
      exact (Set.subset_empty_iff.1 this).symm
    · rw [trigSem_ne _ _ h0]
      exact ⟨⟨κ, hκ, Val.restrict_dom hcov,
        (Formula.sat_congr _ _ _ _ _ fun y hy => hag y hy).2 hκs⟩, hψv⟩
  · rw [Term.evalList_congr _ w _ (fun y hy => hag y (hsub (Or.inr hy)))]; exact ha

end PtIn

namespace TIn
variable (I : U.TIn)

/-- The values in the tables of a history. -/
def TVals (U : Setup Voc) (H : List (ℕ × DB Voc.toSignature)) : Set Voc.𝔻 :=
  {x | ∃ q tr, tr ∈ TablesOf U.L.lets H q ∧ x ∈ tr.2}

/-- **The new rows of a table are bounded.** -/
theorem tab_step {y : Trip Voc} (hy : U.Good y.2.1) (hv : I.VB y) :
    TVals U (I.H ++ [(I.τ, REv.toDB (I.Xof y))]) ⊆ TVals U I.H ∪ I.Wst := by
  rintro x ⟨q, tr, ⟨d, hd, rfl, htr⟩, hx⟩
  obtain ⟨its, hits⟩ := U.items
  obtain ⟨it, -, hspec⟩ := forall₂_mem_left hits d hd
  have hb := U.lets_body d hd
  have hp := U.pastF d hd
  have hfvd := U.wf.fv_let d hd
  have key : ∀ {Φ : Formula Voc} {X : Set Voc.𝕍} {a : Clause Voc}, GuardClause (letM U.Ξ U.T.Γ) X Φ a →
      X = {x | x ∈ d.xs} → Φ.fv ⊆ X → Φ.atoms ⊆ d.φ.atoms → Φ.eqConsts ⊆ d.φ.eqConsts →
      ∀ r ∈ RowsAt (I.St y) I.H.length Φ d.xs, ∀ x ∈ r, x ∈ I.Wst := by
    intro Φ X a ha hXe hX hat heq r hr x hx
    have hrows := rows_guard ha hX (R := fun q => RelOf (I.St y) I.H.length q) (fun _ _ => rfl) d.xs
    rw [hXe] at hrows
    rw [rows_dom_eq (hXe ▸ hX)] at hrows
    rw [← hrows] at hr
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    exact I.WB_Wst _ (I.guard_rows hd ha hX hat heq
      (fun q hq _ => I.rel_all hy hv q (U.letM_GOk hq)) r hr i hi)
  -- a since-shaped let: old rows or new rows of `φr`
  have hsince : ∀ J φl φr, d.φ = .since J φl φr → (∀ r ∈ RowsAt (I.St y) I.H.length φr d.xs,
      ∀ x ∈ r, x ∈ I.Wst) → x ∈ TVals U I.H ∪ I.Wst := by
    intro J φl φr hφ hg
    obtain ⟨h1, h2⟩ := U.tabFor_since I.H I.τ (REv.toDB (I.Xof y)) hφ hp
    rw [h2] at htr
    obtain ⟨m, hm, ht1, ht2, ht3⟩ := htr
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm | rfl
    · left
      refine ⟨d.e, tr, ⟨d, hd, rfl, ?_⟩, hx⟩
      rw [h1]
      exact ⟨m, hm, ht1, ht2, fun m' a b => ht3 m' a (by omega)⟩
    · exact Or.inr (hg _ ht2 x hx)
  cases hspec with
  | once J φ a hχ ha =>
    have hφ := letBody_since hb hχ
    have hfv : φ.fv = {x | x ∈ d.xs} := by
      rw [← hfvd, hφ]; simp [Formula.fv]
    refine hsince J _ φ hφ (key ha hfv le_rfl ?_ ?_)
    · rw [hφ]; exact Set.subset_union_right
    · rw [hφ]; exact Set.subset_union_right
  | since J φl φr a r hχ hne ha hr =>
    have hφ := letBody_since hb hχ
    have hXe : {x | x ∈ d.xs} ∪ (stripExists d.φ).fv = {x | x ∈ d.xs} := by
      rw [hχ, ← hφ, hfvd, Set.union_self]
    have hfv : φr.fv ⊆ {x | x ∈ d.xs} := by
      rw [← hfvd, hφ]; exact Set.subset_union_right
    refine hsince J φl φr hφ (key ha hXe (by rw [hXe]; exact hfv) ?_ ?_)
    · rw [hφ]; exact Set.subset_union_right
    · rw [hφ]; exact Set.subset_union_right
  | prev J φ a hχ ha =>
    have hφ := letBody_prev hb hχ
    have hfv : φ.fv = {x | x ∈ d.xs} := by
      rw [← hfvd, hφ]; rfl
    have hpφ : φ.PastF := by rw [hφ] at hp; exact hp
    rw [U.tabFor_prev (I.H ++ [(I.τ, REv.toDB (I.Xof y))]) 0 ∅ hφ hp] at htr
    obtain ⟨m, hm, -, ht2⟩ := htr
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hm
    subst hm
    have hP := U.SA_snoc_past I.H I.τ (REv.toDB (I.Xof y))
    have : RowsAt (U.SA (I.H ++ [(I.τ, REv.toDB (I.Xof y))]) 0 ∅) I.H.length φ d.xs =
        RowsAt (I.St y) I.H.length φ d.xs := rowsAt_past hP le_rfl hpφ d.xs
    rw [this] at ht2
    refine Or.inr (key ha hfv le_rfl ?_ ?_ _ ht2 x hx)
    · rw [hφ]; exact le_rfl
    · rw [hφ]; exact le_rfl
  | agg ys ω ss gs φ a hχ _ _ _ =>
    have hφ := letBody_agg hb hχ
    unfold TabFor at htr; rw [hφ] at htr; exact absurd htr (Set.notMem_empty _)
  | filt f h1 h2 _ _ _ =>
    unfold TabFor at htr; split at htr
    · next heq => exact absurd (by rw [heq]; rfl) (h1 _ _ _)
    · next heq => exact absurd (by rw [heq]; rfl) (h2 _ _)
    · exact absurd htr (Set.notMem_empty _)
  | plet a h1 h2 _ _ _ =>
    unfold TabFor at htr; split at htr
    · next heq => exact absurd (by rw [heq]; rfl) (h1 _ _ _)
    · next heq => exact absurd (by rw [heq]; rfl) (h2 _ _)
    · exact absurd htr (Set.notMem_empty _)

/-- A sound obligation: a well-typed non-let event, fired by a deferred clause. -/
def ObOK (U : Setup Voc) (o : Obligation Voc) : Prop :=
  (o.1.2.length = Voc.ι o.1.1 ∧ ¬ IsLet U.L.lets o.1.1) ∧
    ∃ c ∈ U.R, c.ε.deferred = true ∧ c.ε.pol = .C ∧ c.ε.name = o.1.1 ∧ Fired U.L.lets c o.1.2

/-- What a call of `Saturate` returns. -/
structure CallOut (Ω₀ : Set (Obligation Voc)) (len : ℕ) (C S : Set (REv Voc))
    (Ω : Set (Obligation Voc)) : Prop where
  goodC : U.Good C
  goodS : U.Good S
  finC : C.Finite
  finΩ : Ω.Finite
  C₀_sub : I.C₀ ⊆ C
  Ω_sub : Ω₀ ⊆ Ω
  disj : ∀ e ∈ S, e ∉ C
  tabs : (TVals U (I.H ++ [(I.τ, REv.toDB ((I.D \ S) ∪ C))])).Finite
  fix : ∀ c ∈ U.R, (I.toPtIn.Δ len c (Ω, C, S)).le (Ω, C, S)
  newΩ : ∀ o ∈ Ω, o ∉ Ω₀ → ObOK U o ∧
    ((∃ n, 1 ≤ n ∧ o.2 = (.ts, I.τ + n)) ∨ (∃ n, 1 ≤ n ∧ o.2 = (.tp, len + n)))
  inC : ∀ e ∈ C, e.1 ∈ U.Ξ.CauAll
  inS : ∀ e ∈ S, e.1 ∈ U.Ξ.Sup
  nameC : ∀ e ∈ C, ∃ c ∈ U.R, c.ε.name = e.1

theorem pol_C_name {c : EClause Voc} (hc : c ∈ U.R) (hp : c.ε.pol = .C) : c.ε.name ∈ U.Ξ.CauAll := by
  have := U.R_ok c hc
  cases hε : c.ε <;> rw [hε] at this hp <;> simp only [Effect.pol, reduceCtorEq] at hp
  · exact this
  · exact this.2
  · exact this.2

/-- **A call of `Saturate`.** -/
theorem call_spec {Ω₀ : Set (Obligation Voc)} (hΩf : Ω₀.Finite)
    (hC₀F : ∀ e ∈ I.C₀, ∃ c ∈ U.R, c.ε.deferred = true ∧ c.ε.pol = .C ∧ c.ε.name = e.1 ∧
      Fired U.L.lets c e.2)
    (TN : Tables Voc) (σ : Trace Voc.toSignature) :
    ∃ C S Ω, Saturate U.P ⟨TablesOf U.L.lets I.H, I.τ, I.D, I.C₀, ∅⟩ TN Ω₀ σ =
        some (TablesOf U.L.lets (I.H ++ [(I.τ, REv.toDB ((I.D \ S) ∪ C))]), C, S, Ω) ∧
      I.CallOut Ω₀ (Trace.len σ) C S Ω := by
  obtain ⟨T', C, S, Ω, hsat, hinv⟩ := I.saturate_some hΩf TN σ
  obtain ⟨g1, g2, g3, g4, g5⟩ := I.toPtIn.saturate_sem σ I.C₀ I.hC₀ Ω₀ TN hsat
  have hcf := I.toPtIn.conflict_free σ I.C₀ I.hC₀ hC₀F Ω₀ TN hsat
  have hF := hinv.mem_F
  have hX : I.toPtIn.Xof (Ω, C, S) = (I.D \ S) ∪ C := rfl
  rw [g3, hX] at hsat
  refine ⟨C, S, Ω, hsat, ?_⟩
  refine ⟨g1, hinv.goodS, I.UE_finite.subset hF.2.1, ?_, g2.2.1, g2.1, hcf, ?_, g4, ?_, ?_, ?_, ?_⟩
  · exact (hΩf.union ((I.UE_finite.prod (I.Dl_finite _)).subset fun _ h => h)).subset hF.1
  · rw [← hX]; exact ((I.hTf.union I.Wst_finite).subset (I.tab_step hinv.goodC hinv.vb))
  · intro o ho hno
    obtain ⟨c, hc, x', -, -, -, hΔ⟩ := g5 (.inl o) ⟨ho, hno⟩
    simp only [PtIn.InΔ, PtIn.Δ] at hΔ
    have hok := U.R_ok c hc
    obtain ⟨⟨-, hnl⟩, -⟩ := U.R_props c hc
    have hlen : o.1.2.length = Voc.ι o.1.1 := by
      rcases hinv.om o ho with h | h
      · exact absurd h hno
      · exact h.1.1
    cases hε : c.ε with
    | cau | sup => rw [hε] at hΔ; exact absurd hΔ (Set.notMem_empty _)
    | ev J e ts =>
      rw [hε] at hΔ hok hnl
      obtain ⟨n, hJ, h1, h2, h3⟩ := hΔ
      obtain ⟨⟨n', hn', hJ'⟩, -⟩ := hok
      rw [hJ'] at hJ; have := icc_inj hJ; subst this
      obtain ⟨w, hw1, hw2, hw3⟩ := I.toPtIn.fired_of_A hc h2
      refine ⟨⟨⟨hlen, by rw [h1]; exact hnl⟩, c, hc, by rw [hε]; rfl, by rw [hε]; rfl,
        by rw [hε, h1]; rfl, _, _, w, hw1, hw2, hw3⟩, Or.inl ⟨n', hn', h3⟩⟩
    | nexts n e ts =>
      rw [hε] at hΔ hok hnl
      obtain ⟨h1, h2, h3⟩ := hΔ
      obtain ⟨w, hw1, hw2, hw3⟩ := I.toPtIn.fired_of_A hc h2
      refine ⟨⟨⟨hlen, by rw [h1]; exact hnl⟩, c, hc, by rw [hε]; rfl, by rw [hε]; rfl,
        by rw [hε, h1]; rfl, _, _, w, hw1, hw2, hw3⟩, Or.inr ⟨n, hok.1, h3⟩⟩
  · intro e he
    by_cases h0 : e ∈ I.C₀
    · obtain ⟨c, hc, -, hp, hn, -⟩ := hC₀F e h0
      rw [← hn]; exact pol_C_name hc hp
    · obtain ⟨c, hc, x', -, -, -, hΔ⟩ := g5 (.inr (.inl e)) ⟨he, h0⟩
      simp only [PtIn.InΔ, PtIn.Δ] at hΔ
      have hok := U.R_ok c hc
      cases hε : c.ε <;> rw [hε] at hΔ hok <;> simp at hΔ
      rw [hΔ.1]; exact hok
  · intro e he
    obtain ⟨c, hc, x', -, -, -, hΔ⟩ := g5 (.inr (.inr e)) ⟨he, Set.notMem_empty _⟩
    simp only [PtIn.InΔ, PtIn.Δ] at hΔ
    have hok := U.R_ok c hc
    cases hε : c.ε <;> rw [hε] at hΔ hok <;> simp at hΔ
    rw [hΔ.1]; exact hok
  · intro e he
    by_cases h0 : e ∈ I.C₀
    · obtain ⟨c, hc, -, -, hn, -⟩ := hC₀F e h0
      exact ⟨c, hc, hn⟩
    · obtain ⟨c, hc, x', -, -, -, hΔ⟩ := g5 (.inr (.inl e)) ⟨he, h0⟩
      simp only [PtIn.InΔ, PtIn.Δ] at hΔ
      refine ⟨c, hc, ?_⟩
      cases hε : c.ε <;> rw [hε] at hΔ <;> simp at hΔ
      rw [hΔ.1]; rfl

end TIn

end Setup

end Paper
