/-
  The value bounds for termination.
-/
import Paper.Proof.DFG

namespace Paper

open Classical

variable {Voc : Vocabulary}

mutual
/-- The constants of a term. -/
def Term.consts : Term Voc → Set Voc.𝔻
  | .var _ => ∅
  | .const c => {c}
  | .app _ ts => Term.constsList ts
def Term.constsList : List (Term Voc) → Set Voc.𝔻
  | [] => ∅
  | t :: ts => Term.consts t ∪ Term.constsList ts
end

mutual
theorem Term.consts_finite : ∀ t : Term Voc, t.consts.Finite
  | .var _ => Set.finite_empty
  | .const _ => Set.finite_singleton _
  | .app _ ts => Term.constsList_finite ts
theorem Term.constsList_finite : ∀ ts : List (Term Voc), (Term.constsList ts).Finite
  | [] => Set.finite_empty
  | t :: ts => (Term.consts_finite t).union (Term.constsList_finite ts)
end

/-- The constants of the equations of a formula. -/
def Formula.eqConsts : Formula Voc → Set Voc.𝔻
  | .eq _ c => {c}
  | .neg φ | .ex _ φ | .next _ φ | .prev _ φ | .eventually _ φ | .agg _ _ _ _ φ => φ.eqConsts
  | .and φ ψ | .since _ φ ψ | .letin _ _ φ ψ => φ.eqConsts ∪ ψ.eqConsts
  | _ => ∅

theorem eqConsts_finite : ∀ φ : Formula Voc, φ.eqConsts.Finite
  | .eq _ _ => Set.finite_singleton _
  | .neg φ | .ex _ φ | .next _ φ | .prev _ φ | .eventually _ φ | .agg _ _ _ _ φ => eqConsts_finite φ
  | .and φ ψ | .since _ φ ψ | .letin _ _ φ ψ => (eqConsts_finite φ).union (eqConsts_finite ψ)
  | .top | .pred .. => Set.finite_empty

/-- Valuations on `F` with values in `X`. -/
def ValsIn (F : Set Voc.𝕍) (X : Set Voc.𝔻) : Set (Val Voc) :=
  {v | v.dom = F ∧ ∀ x ∈ F, ∃ a ∈ X, v x = some a}

theorem ValsIn_mono {F : Set Voc.𝕍} {X Y : Set Voc.𝔻} (h : X ⊆ Y) : ValsIn F X ⊆ ValsIn F Y := by
  rintro v ⟨h1, h2⟩; exact ⟨h1, fun x hx => let ⟨a, ha, h3⟩ := h2 x hx; ⟨a, h ha, h3⟩⟩

theorem ValsIn_finite {F : Set Voc.𝕍} {X : Set Voc.𝔻} (hF : F.Finite) (hX : X.Finite) :
    (ValsIn F X).Finite := by
  haveI := hF.to_subtype
  refine Set.Finite.of_finite_image (f := fun v : Val Voc => fun x : F => v x) ?_ ?_
  · refine (Set.Finite.pi (t := fun _ : F => some '' X) fun _ => hX.image _).subset ?_
    rintro g ⟨v, ⟨-, hv⟩, rfl⟩ x -
    obtain ⟨a, ha, h⟩ := hv x x.2; exact ⟨a, ha, h.symm⟩
  · rintro v ⟨hv1, -⟩ w ⟨hw1, -⟩ h
    funext x
    by_cases hx : x ∈ F
    · exact congrFun h ⟨x, hx⟩
    · have h1 : x ∉ v.dom := by rw [hv1]; exact hx
      have h2 : x ∉ w.dom := by rw [hw1]; exact hx
      simp only [Val.dom, Set.mem_setOf_eq, Option.not_isSome_iff_eq_none] at h1 h2
      rw [h1, h2]

/-- The stable part of a term's value. -/
theorem stable_eval (O : StabOrder Voc) (v : Val Voc) :
    ∀ (t : Term Voc), (∀ f ∈ t.funs, Stable O f) → ∀ d, t.eval v = some d →
      (∃ x ∈ t.vars, ∃ a, v x = some a ∧ (d = a ∨ O.le d a)) ∨
        (∃ c ∈ t.consts, d = c ∨ O.le d c) := by
  intro t
  refine Term.rec (motive_1 := fun t => (∀ f ∈ t.funs, Stable O f) → ∀ d, t.eval v = some d →
      (∃ x ∈ t.vars, ∃ a, v x = some a ∧ (d = a ∨ O.le d a)) ∨ (∃ c ∈ t.consts, d = c ∨ O.le d c))
    (motive_2 := fun ts => (∀ f ∈ Term.funsList ts, Stable O f) → ∀ ds,
      Term.evalList v ts = some ds → ∀ k (hk : k < ds.length),
        (∃ x ∈ Term.varsList ts, ∃ a, v x = some a ∧ (ds[k] = a ∨ O.le ds[k] a)) ∨
          (∃ c ∈ Term.constsList ts, ds[k] = c ∨ O.le ds[k] c)) ?_ ?_ ?_ ?_ ?_ t
  · intro x _ d h
    exact Or.inl ⟨x, by simp [Term.vars], d, h, Or.inl rfl⟩
  · intro c _ d h
    simp [Term.eval] at h; subst h
    exact Or.inr ⟨c, by simp [Term.consts], Or.inl rfl⟩
  · intro f ts ih hst d h
    simp only [Term.eval, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ds, hds, a, ha, rfl⟩ := h
    obtain ⟨k, hk⟩ := hst f (by simp [Term.funs]) a
    have hl : ds.length = Voc.ιF f := by
      unfold toVec at ha; split_ifs at ha with h; exact h
    have hak : a k = ds[k.1]'(by rw [hl]; exact k.2) := by
      unfold toVec at ha; split_ifs at ha with h; simp at ha; rw [← ha]
    rcases ih (fun g hg => hst g (by simp [Term.funs, hg])) ds hds k.1 (by rw [hl]; exact k.2) with
      ⟨x, hx, b, hb, hd⟩ | ⟨c, hc, hd⟩
    · refine Or.inl ⟨x, hx, b, hb, Or.inr ?_⟩
      rw [← hak] at hd
      rcases hd with hd | hd
      · rw [← hd]; exact hk
      · exact O.trans _ _ _ hk hd
    · refine Or.inr ⟨c, hc, Or.inr ?_⟩
      rw [← hak] at hd
      rcases hd with hd | hd
      · rw [← hd]; exact hk
      · exact O.trans _ _ _ hk hd
  · intro _ ds h k hk; simp [Term.evalList] at h; subst h; simp at hk
  · intro t ts ih1 ih2 hst ds h k hk
    simp only [Term.evalList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨d, hd, ds', hds', rfl⟩ := h
    rcases k with _ | k
    · rcases ih1 (fun g hg => hst g (Or.inl hg)) d hd with ⟨x, hx, b, hb, h⟩ | ⟨c, hc, h⟩
      · exact Or.inl ⟨x, Or.inl hx, b, hb, h⟩
      · exact Or.inr ⟨c, Or.inl hc, h⟩
    · rcases ih2 (fun g hg => hst g (Or.inr hg)) ds' hds' k (by simpa using hk) with
        ⟨x, hx, b, hb, h⟩ | ⟨c, hc, h⟩
      · exact Or.inl ⟨x, Or.inr hx, b, hb, h⟩
      · exact Or.inr ⟨c, Or.inr hc, h⟩

namespace Setup
variable (U : Setup Voc)

/-- Values of terms over inputs in `X`. -/
def TermΦ (X : Set Voc.𝔻) : Set Voc.𝔻 :=
  {d | ∃ c ∈ U.R, ∃ t ∈ c.ε.args, ∃ v ∈ ValsIn t.vars X, t.eval v = some d}

/-- The aggregation of a valuation set. -/
def AggOf (ω : Voc.Ω) (ss : List (Term Voc)) (G : Finset (Val Voc)) : Set Voc.𝔻 :=
  {d | ∃ M : Multiset (Fin (Voc.ι' ω).1 → Voc.𝔻),
    M.map some = G.val.map (fun v => (Term.evalList v ss).bind (toVec _)) ∧
    ∃ w ∈ Voc.ωhat ω M, d ∈ List.ofFn w}

/-- Aggregation results over inputs in `X`. -/
def AggΦ (X : Set Voc.𝔻) : Set Voc.𝔻 :=
  {d | ∃ dl ∈ U.L.lets, ∃ ys ω ss gs φ, dl.φ = .agg ys ω ss gs φ ∧
    ∃ G : Finset (Val Voc), ↑G ⊆ ValsIn φ.fv X ∧ d ∈ AggOf ω ss G}

/-- The productions over inputs in `X`. -/
def Φ (X : Set Voc.𝔻) : Set Voc.𝔻 := U.TermΦ X ∪ U.AggΦ X

theorem Φ_mono {X Y : Set Voc.𝔻} (h : X ⊆ Y) : U.Φ X ⊆ U.Φ Y := by
  rintro d (⟨c, hc, t, ht, v, hv, he⟩ | ⟨dl, hdl, ys, ω, ss, gs, φ, hφ, G, hG, hd⟩)
  · exact Or.inl ⟨c, hc, t, ht, v, ValsIn_mono h hv, he⟩
  · exact Or.inr ⟨dl, hdl, ys, ω, ss, gs, φ, hφ, G, hG.trans (ValsIn_mono h), hd⟩

theorem AggOf_finite (ω : Voc.Ω) (ss : List (Term Voc)) (G : Finset (Val Voc)) :
    (AggOf ω ss G).Finite := by
  by_cases hM : ∃ M : Multiset (Fin (Voc.ι' ω).1 → Voc.𝔻),
      M.map some = G.val.map (fun v => (Term.evalList v ss).bind (toVec _))
  · obtain ⟨M, hM⟩ := hM
    refine (((Voc.ωhat ω M).finite_toSet).biUnion fun w _ => (List.finite_toSet (List.ofFn w))).subset ?_
    rintro d ⟨M', hM', w, hw, hd⟩
    have : M' = M := Multiset.map_injective (Option.some_injective _) (hM'.trans hM.symm)
    subst this
    exact Set.mem_biUnion hw hd
  · exact Set.finite_empty.subset fun d ⟨M, hM', _⟩ => absurd ⟨M, hM'⟩ hM

theorem finsets_sub_finite {α : Type} {V : Set α} (hV : V.Finite) :
    {G : Finset α | ↑G ⊆ V}.Finite := by
  refine (hV.toFinset.powerset.finite_toSet).subset fun G hG => ?_
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
  intro x hx; simpa using hG hx

theorem Φ_finite {X : Set Voc.𝔻} (hX : X.Finite) : (U.Φ X).Finite := by
  refine Set.Finite.union ?_ ?_
  · refine (U.R_finite.biUnion fun c _ => (List.finite_toSet c.ε.args).biUnion fun t _ =>
      (ValsIn_finite (Term.vars_finite t) hX).biUnion fun v _ =>
        (Set.Subsingleton.finite (s := {d | t.eval v = some d}) fun a ha b hb => by
          simp only [Set.mem_setOf_eq] at ha hb; rw [ha] at hb; exact Option.some.inj hb)).subset ?_
    rintro d ⟨c, hc, t, ht, v, hv, he⟩
    exact Set.mem_biUnion hc (Set.mem_biUnion ht (Set.mem_biUnion hv he))
  · have hdl : ∀ dl : LetDef Voc, {d | ∃ ys ω ss gs φ, dl.φ = .agg ys ω ss gs φ ∧
        ∃ G : Finset (Val Voc), ↑G ⊆ ValsIn φ.fv X ∧ d ∈ AggOf ω ss G}.Finite := by
      intro dl
      cases hφ : dl.φ with
      | agg ys ω ss gs φ =>
        refine ((finsets_sub_finite (ValsIn_finite (Formula.fv_finite φ) hX)).biUnion
          fun G _ => AggOf_finite ω ss G).subset ?_
        rintro d ⟨ys', ω', ss', gs', φ', he, G, hG, hd⟩
        simp only [Formula.agg.injEq] at he
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
        exact Set.mem_biUnion hG hd
      | _ => exact Set.finite_empty.subset fun d ⟨_, _, _, _, _, he, _⟩ => by cases he
    refine ((List.finite_toSet U.L.lets).biUnion fun dl _ => hdl dl).subset ?_
    rintro d ⟨dl, hdlm, ys, ω, ss, gs, φ, hφ, G, hG, hd⟩
    exact Set.mem_biUnion hdlm ⟨ys, ω, ss, gs, φ, hφ, G, hG, hd⟩

/-- The constants of `R` and of the lets. -/
def Consts : Set Voc.𝔻 :=
  (⋃ c ∈ U.R, c.trig.eqConsts ∪ ⋃ t ∈ {t | t ∈ c.ε.args}, t.consts) ∪
    ⋃ dl ∈ {dl | dl ∈ U.L.lets}, dl.φ.eqConsts

theorem Consts_finite : U.Consts.Finite :=
  (U.R_finite.biUnion fun c _ => (eqConsts_finite _).union
    ((List.finite_toSet _).biUnion fun t _ => Term.consts_finite t)).union
    ((List.finite_toSet _).biUnion fun _ _ => eqConsts_finite _)

end Setup

end Paper
