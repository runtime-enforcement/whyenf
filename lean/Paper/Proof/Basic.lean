/-
  Basic lemmas used by the proof of Theorem 4.3.
-/
import Paper.Proof.Claims

namespace Paper

variable {Voc : Vocabulary}

theorem mapM_forall₂ {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → List.Forall₂ (fun x y => f x = some y) xs ys
  | [], ys, h => by simp at h; subst h; exact .nil
  | x :: xs, ys, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys', hys, rfl⟩ := h
    exact .cons hy (mapM_forall₂ hys)

/-! ## Valuations -/

@[simp] theorem Val.upd_same (v : Val Voc) (x : Voc.𝕍) (d : Voc.𝔻) : v.upd x d x = some d := by
  simp [Val.upd]

theorem Val.upd_ne (v : Val Voc) {x y : Voc.𝕍} (d : Voc.𝔻) (h : y ≠ x) : v.upd x d y = v y := by
  simp [Val.upd, Function.update_of_ne h]

theorem Val.upd_upd (v : Val Voc) (x : Voc.𝕍) (d e : Voc.𝔻) : (v.upd x d).upd x e = v.upd x e := by
  simp [Val.upd]

theorem Val.upd_comm (v : Val Voc) {x y : Voc.𝕍} (d e : Voc.𝔻) (h : x ≠ y) :
    (v.upd x d).upd y e = (v.upd y e).upd x d := by
  simp [Val.upd, Function.update_comm h]

theorem Val.upd_eq_self (v : Val Voc) {x : Voc.𝕍} {d : Voc.𝔻} (h : v x = some d) : v.upd x d = v := by
  simp [Val.upd, ← h]

/-! ## Substitution -/

mutual
theorem Term.eval_subst (d : Voc.𝔻) (x : Voc.𝕍) (w : Val Voc) :
    ∀ t : Term Voc, (t.subst d x).eval w = t.eval (w.upd x d)
  | .var y => by
    by_cases h : y = x
    · subst h; simp [Term.subst, Term.eval]
    · simp [Term.subst, Term.eval, h, Val.upd_ne _ _ h]
  | .const _ => rfl
  | .app f ts => by simp only [Term.subst, Term.eval]; rw [Term.evalList_subst d x w ts]
theorem Term.evalList_subst (d : Voc.𝔻) (x : Voc.𝕍) (w : Val Voc) :
    ∀ ts : List (Term Voc), Term.evalList w (Term.substList d x ts) = Term.evalList (w.upd x d) ts
  | [] => rfl
  | t :: ts => by
    simp only [Term.substList, Term.evalList]; rw [Term.eval_subst d x w t, Term.evalList_subst d x w ts]
end

mutual
theorem Term.vars_subst (d : Voc.𝔻) (x : Voc.𝕍) :
    ∀ t : Term Voc, (t.subst d x).vars = t.vars \ {x}
  | .var y => by
    by_cases h : y = x
    · subst h; simp [Term.subst, Term.vars]
    · simp only [Term.subst, h, ↓reduceIte, Term.vars]
      rw [Set.sdiff_singleton_eq_self]; simpa using Ne.symm h
  | .const _ => by simp [Term.subst, Term.vars]
  | .app f ts => by simp only [Term.subst, Term.vars]; exact Term.varsList_subst d x ts
theorem Term.varsList_subst (d : Voc.𝔻) (x : Voc.𝕍) :
    ∀ ts : List (Term Voc), Term.varsList (Term.substList d x ts) = Term.varsList ts \ {x}
  | [] => by simp [Term.substList, Term.varsList]
  | t :: ts => by
    simp only [Term.substList, Term.varsList]
    rw [Term.vars_subst d x t, Term.varsList_subst d x ts, Set.union_sdiff_distrib]
end

theorem Formula.subst_spec (d : Voc.𝔻) (x : Voc.𝕍) :
    ∀ (φ φ' : Formula Voc), φ.subst d x = some φ' →
      φ'.fv = φ.fv \ {x} ∧ ∀ S w i, φ'.sat S w i ↔ φ.sat S (w.upd x d) i := by
  intro φ
  induction φ with
  | top => intro φ' h; cases h; simp [Formula.fv, Formula.sat]
  | pred e ts =>
    intro φ' h; cases h
    refine ⟨Term.varsList_subst d x ts, fun S w i => ?_⟩
    simp only [Formula.sat, Term.evalList_subst]
  | neg φ ih =>
    intro φ' h
    simp only [Formula.subst, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨ψ, hψ, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih ψ hψ
    exact ⟨h1, fun S w i => by simp only [Formula.sat, h2]⟩
  | and φ ψ ih₁ ih₂ =>
    intro φ' h
    simp only [Formula.subst] at h
    cases h₁ : φ.subst d x <;> cases h₂ : ψ.subst d x <;>
      simp [h₁, h₂, Seq.seq, Option.map_eq_map] at h
    subst h
    obtain ⟨a1, a2⟩ := ih₁ _ h₁; obtain ⟨b1, b2⟩ := ih₂ _ h₂
    exact ⟨by simp [Formula.fv, a1, b1, Set.union_sdiff_distrib],
      fun S w i => by simp only [Formula.sat, a2, b2]⟩
  | ex y φ ih =>
    intro φ' h
    simp only [Formula.subst] at h
    by_cases hy : y = x
    · subst hy; simp at h; subst h
      refine ⟨by simp [Formula.fv], fun S w i => ?_⟩
      simp only [Formula.sat, Val.upd_upd]
    · simp only [hy, ↓reduceIte, Option.map_eq_map, Option.map_eq_some_iff] at h
      obtain ⟨ψ, hψ, rfl⟩ := h
      obtain ⟨h1, h2⟩ := ih ψ hψ
      refine ⟨by simp only [Formula.fv, h1]; ext z; simp; tauto, fun S w i => ?_⟩
      simp only [Formula.sat, h2, Val.upd_comm _ _ _ (Ne.symm hy)]
  | next I φ ih =>
    intro φ' h
    simp only [Formula.subst, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨ψ, hψ, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih ψ hψ
    exact ⟨h1, fun S w i => by simp only [Formula.sat, h2]⟩
  | prev I φ ih =>
    intro φ' h
    simp only [Formula.subst, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨ψ, hψ, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih ψ hψ
    exact ⟨h1, fun S w i => by simp only [Formula.sat, h2]⟩
  | eventually I φ ih =>
    intro φ' h
    simp only [Formula.subst, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨ψ, hψ, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih ψ hψ
    exact ⟨h1, fun S w i => by simp only [Formula.sat, h2]⟩
  | since I φ ψ ih₁ ih₂ =>
    intro φ' h
    simp only [Formula.subst] at h
    cases h₁ : φ.subst d x <;> cases h₂ : ψ.subst d x <;>
      simp [h₁, h₂, Seq.seq, Option.map_eq_map] at h
    subst h
    obtain ⟨a1, a2⟩ := ih₁ _ h₁; obtain ⟨b1, b2⟩ := ih₂ _ h₂
    exact ⟨by simp [Formula.fv, a1, b1, Set.union_sdiff_distrib],
      fun S w i => by simp only [Formula.sat, a2, b2]⟩
  | letin e xs φ ψ _ ih₂ =>
    intro φ' h
    simp only [Formula.subst, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨χ, hχ, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih₂ χ hχ
    exact ⟨h1, fun S w i => by simp only [Formula.sat]; exact h2 _ _ _⟩
  | agg ys ω ss gs φ _ =>
    intro φ' h
    simp only [Formula.subst] at h
    split_ifs at h with hx
    cases h
    push Not at hx
    have hfv : x ∉ (Formula.agg ys ω ss gs φ).fv := by
      simp [Formula.fv]; exact ⟨hx.2, hx.1⟩
    refine ⟨by simp [Set.sdiff_singleton_eq_self hfv], fun S w i => ?_⟩
    refine Formula.sat_congr _ S w (w.upd x d) i fun z hz => ?_
    have : z ≠ x := fun h => hfv (h ▸ hz)
    rw [Val.upd_ne _ _ this]
  | eq y c =>
    intro φ' h
    simp only [Formula.subst] at h
    split_ifs at h with hy
    cases h
    refine ⟨by simp only [Formula.fv]; rw [Set.sdiff_singleton_eq_self]; simpa using Ne.symm hy,
      fun S w i => ?_⟩
    simp only [Formula.sat, Val.upd_ne _ _ hy]

theorem GAtom.subst_spec {d : Voc.𝔻} {x : Voc.𝕍} {γ γ' : GAtom Voc} (h : γ.subst d x = some γ') :
    γ'.toFormula.fv = γ.toFormula.fv \ {x} ∧
      ∀ S w i, γ'.toFormula.sat S w i ↔ γ.toFormula.sat S (w.upd x d) i := by
  cases γ with
  | pred p ts =>
    simp only [GAtom.subst, Option.some.injEq] at h; subst h
    exact Formula.subst_spec d x (.pred p ts) _ rfl
  | eq y c =>
    simp only [GAtom.subst] at h
    split_ifs at h with hy; cases h
    exact Formula.subst_spec d x (.eq y c) _ (by simp [Formula.subst, hy, GAtom.toFormula])

theorem GConj.subst_spec {d : Voc.𝔻} {x : Voc.𝕍} :
    ∀ {κ κ' : GConj Voc}, List.Forall₂ (fun γ γ' => γ.subst d x = some γ') κ κ' →
      κ'.toFormula.fv = κ.toFormula.fv \ {x} ∧
        ∀ S w i, κ'.toFormula.sat S w i ↔ κ.toFormula.sat S (w.upd x d) i
  | [], [], .nil => by simp [GConj.toFormula, Formula.fv, Formula.sat]
  | γ :: κ, γ' :: κ', .cons h hs => by
    obtain ⟨a1, a2⟩ := GAtom.subst_spec h
    obtain ⟨b1, b2⟩ := GConj.subst_spec hs
    simp only [GConj.toFormula, List.foldr_cons, Formula.fv, Formula.sat] at b1 b2 ⊢
    exact ⟨by rw [a1, b1, Set.union_sdiff_distrib], fun S w i => by rw [a2, b2]⟩

theorem GDisj.subst_spec' {d : Voc.𝔻} {x : Voc.𝕍} :
    ∀ {π π' : GDisj Voc},
      List.Forall₂ (fun κ κ' => List.Forall₂ (fun γ γ' => γ.subst d x = some γ') κ κ') π π' →
      π'.toFormula.fv = π.toFormula.fv \ {x} ∧
        ∀ S w i, π'.toFormula.sat S w i ↔ π.toFormula.sat S (w.upd x d) i
  | [], [], .nil => by simp [GDisj.toFormula, Formula.bot, Formula.fv, Formula.sat]
  | κ :: π, κ' :: π', .cons h hs => by
    obtain ⟨a1, a2⟩ := GConj.subst_spec h
    obtain ⟨b1, b2⟩ := GDisj.subst_spec' hs
    simp only [GDisj.toFormula, List.foldr_cons, Formula.or, Formula.fv, Formula.sat] at b1 b2 ⊢
    exact ⟨by rw [a1, b1, Set.union_sdiff_distrib], fun S w i => by rw [a2, b2]⟩

theorem GDisj.subst_spec {d : Voc.𝔻} {x : Voc.𝕍} {π π' : GDisj Voc} (h : π.subst d x = some π') :
    π'.toFormula.fv = π.toFormula.fv \ {x} ∧
      ∀ S w i, π'.toFormula.sat S w i ↔ π.toFormula.sat S (w.upd x d) i := by
  apply GDisj.subst_spec'
  have := mapM_forall₂ h
  exact this.imp fun κ κ' hκ => mapM_forall₂ hκ

theorem Effect.subst_name (d : Voc.𝔻) (x : Voc.𝕍) (ε : Effect Voc) : (ε.subst d x).name = ε.name := by
  cases ε <;> rfl

theorem Effect.subst_args (d : Voc.𝔻) (x : Voc.𝕍) (ε : Effect Voc) :
    (ε.subst d x).args = Term.substList d x ε.args := by
  cases ε <;> rfl

/-! ## Big conjunctions, tensors, `○ⁿ` -/

theorem fv_bigAnd : ∀ φs : List (Formula Voc), (bigAnd φs).fv = {x | ∃ φ ∈ φs, x ∈ φ.fv}
  | [] => by simp [bigAnd, Formula.fv]
  | [φ] => by simp [bigAnd]
  | φ :: ψ :: φs => by
    rw [show bigAnd (φ :: ψ :: φs) = .and φ (bigAnd (ψ :: φs)) from rfl]
    simp only [Formula.fv, fv_bigAnd (ψ :: φs)]
    ext x; simp

theorem mem_bigTensor : ∀ {𝒞s : List (CSet Voc)} {C : Set (EClause Voc)}, C ∈ CSet.bigTensor 𝒞s →
    ∃ Cs : List (Set (EClause Voc)), List.Forall₂ (· ∈ ·) Cs 𝒞s ∧ ∀ C' ∈ Cs, C' ⊆ C
  | [], C, h => ⟨[], .nil, by simp⟩
  | 𝒞 :: 𝒞s, C, h => by
    obtain ⟨C₁, h₁, C₂, h₂, rfl⟩ := h
    obtain ⟨Cs, hCs, hsub⟩ := mem_bigTensor h₂
    refine ⟨C₁ :: Cs, .cons h₁ hCs, ?_⟩
    intro C' hC'
    rcases List.mem_cons.1 hC' with rfl | hC'
    · exact Set.subset_union_left
    · exact (hsub C' hC').trans Set.subset_union_right

theorem sat_nextN (S : Str Voc.toSignature) (v : Val Voc) (φ : Formula Voc) :
    ∀ n i, (nextN n φ).sat S v i ↔ φ.sat S v (i + n)
  | 0, i => by simp [nextN]
  | n + 1, i => by
    rw [nextN, Function.iterate_succ_apply']
    simp only [Formula.sat, Interval.mem_univ, and_true]
    rw [← nextN, sat_nextN S v φ n (i + 1)]
    ring_nf

theorem fv_nextN (φ : Formula Voc) : ∀ n, (nextN n φ).fv = φ.fv
  | 0 => rfl
  | n + 1 => by rw [nextN, Function.iterate_succ_apply']; simp only [Formula.fv]; exact fv_nextN φ n

/-! ## Guard extraction keeps the meaning and the variables -/

theorem GX.fv_filter {m : Set Voc.ℰ} {p X Φ π φ} (h : GX m p X Φ π φ) : φ.fv ⊆ Φ.fv := by
  induction h with
  | none => exact le_rfl
  | vac => simp [Formula.fv]
  | pred => simp [Formula.fv]
  | eq => simp [Formula.fv]
  | andPos _ _ _ ih₁ ih₂ => exact Set.union_subset_union ih₁ ih₂
  | @andNeg X φ ψ φ' ψ' π₁ π₂ h₁ h₂ ih₁ ih₂ =>
    simp only [Formula.imp, Formula.or, Formula.fv]
    have g₁ : π₁.toFormula.fv ⊆ φ.fv := by
      rw [fv_gdisj]; rintro x ⟨κ, hκ, hx⟩; exact h₁.fv_sub κ hκ hx
    have g₂ : π₂.toFormula.fv ⊆ ψ.fv := by
      rw [fv_gdisj]; rintro x ⟨κ, hκ, hx⟩; exact h₂.fv_sub κ hκ hx
    exact Set.union_subset_union (Set.union_subset g₁ ih₁) (Set.union_subset g₂ ih₂)
  | neg _ ih => exact ih

theorem fv_prod (π₁ π₂ : GDisj Voc) :
    (π₁.prod π₂).toFormula.fv ⊆ π₁.toFormula.fv ∪ π₂.toFormula.fv := by
  rw [fv_gdisj, fv_gdisj, fv_gdisj]
  rintro x ⟨κ, hκ, hx⟩
  simp only [GDisj.prod, List.mem_flatMap, List.mem_map] at hκ
  obtain ⟨κ₁, h₁, κ₂, h₂, rfl⟩ := hκ
  rw [fv_gconj] at hx
  obtain ⟨γ, hγ, hx⟩ := hx
  rcases List.mem_append.1 hγ with hγ | hγ
  · exact Or.inl ⟨κ₁, h₁, by rw [fv_gconj]; exact ⟨γ, hγ, hx⟩⟩
  · exact Or.inr ⟨κ₂, h₂, by rw [fv_gconj]; exact ⟨γ, hγ, hx⟩⟩

theorem GConj.binds_append_left {κ₁ : GConj Voc} (κ₂ : GConj Voc) {x : Voc.𝕍} (h : κ₁.Binds x) :
    (κ₁ ++ κ₂).Binds x := by
  obtain ⟨γ, hγ, h⟩ := h; exact ⟨γ, List.mem_append_left _ hγ, h⟩

theorem GConj.binds_append_right (κ₁ : GConj Voc) {κ₂ : GConj Voc} {x : Voc.𝕍} (h : κ₂.Binds x) :
    (κ₁ ++ κ₂).Binds x := by
  obtain ⟨γ, hγ, h⟩ := h; exact ⟨γ, List.mem_append_right _ hγ, h⟩

/-- `(π, ψ) ⇝⁺_x (π', ψ')` keeps the meaning of the trigger, does not add
    variables, and makes `π'` bind `x`. -/
theorem TGX.spec {m : Set Voc.ℰ} {x : Voc.𝕍} {π π' : GDisj Voc} {ψ ψ' : Formula Voc}
    (h : TGX m .pos x π ψ π' ψ') :
    Equiv (.and π'.toFormula ψ') (.and π.toFormula ψ) ∧
      (Formula.and π'.toFormula ψ').fv ⊆ (Formula.and π.toFormula ψ).fv ∧ ∀ κ ∈ π', κ.Binds x := by
  cases h with
  | bound hb => exact ⟨fun _ _ _ => Iff.rfl, le_rfl, hb⟩
  | @filter π₀ _ hg =>
    obtain ⟨hb, he⟩ := hg.sound
    refine ⟨fun σ v i => ?_, ?_, ?_⟩
    · have := he σ v i
      simp only [Formula.sat, sat_prod] at this ⊢
      rw [← this]; tauto
    · simp only [Formula.fv]
      have h0 : π₀.toFormula.fv ⊆ ψ.fv := by
        rw [fv_gdisj]; rintro y ⟨κ, hκ, hy⟩; exact hg.fv_sub κ hκ hy
      exact Set.union_subset ((fv_prod π π₀).trans (Set.union_subset_union le_rfl h0))
        (hg.fv_filter.trans Set.subset_union_right)
    · intro κ hκ
      simp only [GDisj.prod, List.mem_flatMap, List.mem_map] at hκ
      obtain ⟨κ₁, h₁, κ₂, h₂, rfl⟩ := hκ
      exact GConj.binds_append_right _ (hb κ₂ h₂ x rfl)

end Paper
