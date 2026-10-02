/-
  The EF interpretation of the compiled program is the MFOTL semantics of the
  lets (on histories).
-/
import Paper.Proof.Eval

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem LetItemSpec.pastF {Ξ : RwSetting Voc} {Γ : LetCtx Voc} {colTy : Voc.𝕍 → Ty} {d : LetDef Voc} {it : Item Voc}
    (h : LetItemSpec Ξ Γ colTy d it) (hb : d.φ.IsLetBody) : d.φ.PastF := by
  cases h with
  | once I φ a hχ ha =>
    rw [letBody_since hb hχ]; exact ⟨trivial, ha.basic.pastF⟩
  | prev I φ a hχ ha => rw [letBody_prev hb hχ]; exact ha.basic.pastF
  | agg ys ω ss gs φ a hχ _ _ ha => rw [letBody_agg hb hχ]; exact ha.basic.pastF
  | since I φl φr a r hχ _ ha hr =>
    rw [letBody_since hb hχ]
    exact ⟨(show (Formula.neg φl).Basic from hr.basic).pastF, ha.basic.pastF⟩
  | filt f _ _ _ _ hf =>
    obtain ⟨ys, hys⟩ := exs_stripExists d.φ
    rw [hys]; exact exs_pastF ys (toFilter_basic hf).pastF
  | plet a _ _ _ _ ha =>
    obtain ⟨ys, hys⟩ := exs_stripExists d.φ
    rw [hys]; exact exs_pastF ys ha.basic.pastF

namespace Setup
variable (U : Setup Voc)

theorem items : ∃ its : List (Item Voc),
    List.Forall₂ (fun d it => LetItemSpec U.Ξ U.T.Γ U.colTy d it) U.L.lets its := by
  obtain ⟨its, -, h, -, -⟩ := U.compile_spec; exact ⟨its, h⟩

theorem pastF : ∀ d ∈ U.L.lets, d.φ.PastF := by
  obtain ⟨its, h⟩ := U.items
  intro d hd
  obtain ⟨it, -, hit⟩ := forall₂_mem_left h d hd
  exact hit.pastF (U.lets_body d hd)

/-- The let semantics as rows. -/
theorem relOf_let (S₀ : Str Voc.toSignature) (h₀ : ∀ j, ∀ ev ∈ S₀.D j, ¬ IsLet U.L.lets ev.e)
    {d : LetDef Voc} (hd : d ∈ U.L.lets) (j : ℕ) :
    RelOf (applyLets U.L.lets S₀) j d.e = DefRows (applyLets U.L.lets S₀) j d.φ d.xs := by
  have hAL := applyLets_spec' U.L.lets U.wf.nodup U.scope_names S₀ h₀ U.L.lets.length le_rfl
  rw [List.take_length] at hAL
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  have hdef := hAL.2.2 k hk hk
  ext r
  simp only [RelOf, DefRows, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ev, hev, he, rfl⟩; exact (hdef j ev he).1 hev
  · rintro ⟨v', hc, hv, hs⟩
    have hlen : r.length = Voc.ι U.L.lets[k].e := by
      rw [len_of_map hv, U.wf.arity_let _ hd]
    exact ⟨⟨_, r, hlen⟩, (hdef j _ rfl).2 ⟨v', hc, hv, hs⟩, rfl, rfl⟩

theorem applyLets_τ : ∀ (ℒ : List (LetDef Voc)) (S : Str Voc.toSignature), (applyLets ℒ S).τ = S.τ
  | [], _ => rfl
  | d :: ℒ, S => by
    simp only [applyLets, List.foldl_cons]; rw [← applyLets, applyLets_τ ℒ]; rfl

theorem letCols_names (Γ : LetCtx Voc) (colTy : Voc.𝕍 → Ty) (d : LetDef Voc) :
    (letCols colTy d).map Col.name = d.xs := by
  simp [letCols, Function.comp_def]

section hist
variable (H : List (ℕ × DB Voc.toSignature)) (τ : ℕ) (D : DB Voc.toSignature)

/-- The let structure of a history with current time-point `(τ, D)`. -/
noncomputable def SA : Str Voc.toSignature := applyLets U.L.lets (strOf H τ D)

theorem SA_τ (m : ℕ) : (U.SA H τ D).τ m = (strOf H τ D).τ m := by
  have hAL := applyLets_τ U.L.lets (strOf H τ D)
  simp only [SA, hAL]

theorem SA_past {m : ℕ} (hm : m < H.length) :
    PastAgree (applyLets U.L.lets (strOf H 0 ∅)) (U.SA H τ D) m :=
  applyLets_past U.L.lets U.pastF (strOf_past H 0 ∅ τ D hm)

theorem SA_snoc_past :
    PastAgree (applyLets U.L.lets (strOf (H ++ [(τ, D)]) 0 ∅)) (U.SA H τ D) H.length := by
  have := applyLets_past U.L.lets U.pastF (strOf_snoc_past H τ D 0 ∅)
  intro k hk; exact ⟨(this k hk).1.symm, (this k hk).2.symm⟩

theorem rowsAt_past {m j : ℕ} {S S' : Str Voc.toSignature} (h : PastAgree S S' j) (hm : m ≤ j)
    {φ : Formula Voc} (hφ : φ.PastF) (xs : List Voc.𝕍) : RowsAt S m φ xs = RowsAt S' m φ xs :=
  RowsAt.congr fun v => hφ.sat_congr h m hm v

theorem tabFor_since {d : LetDef Voc} {I : Interval} {φl φr : Formula Voc}
    (hφ : d.φ = .since I φl φr) (hp : d.φ.PastF) :
    TabFor U.L.lets H d = {tr | ∃ m < H.length, tr.1 = (U.SA H τ D).τ m ∧
        tr.2 ∈ RowsAt (U.SA H τ D) m φr d.xs ∧
        ∀ m', m < m' → m' < H.length → tr.2 ∈ RowsAt (U.SA H τ D) m' φl d.xs} ∧
    TabFor U.L.lets (H ++ [(τ, D)]) d = {tr | ∃ m < H.length + 1, tr.1 = (U.SA H τ D).τ m ∧
        tr.2 ∈ RowsAt (U.SA H τ D) m φr d.xs ∧
        ∀ m', m < m' → m' < H.length + 1 → tr.2 ∈ RowsAt (U.SA H τ D) m' φl d.xs} := by
  rw [hφ] at hp
  constructor
  · unfold TabFor; rw [hφ]; simp only
    ext tr; simp only [Set.mem_setOf_eq]
    refine exists_congr fun m => ?_
    constructor
    · rintro ⟨hm, h1, h2, h3⟩
      refine ⟨hm, ?_, (rowsAt_past (U.SA_past H τ D hm) le_rfl hp.2 _) ▸ h2, fun m' a b =>
        (rowsAt_past (U.SA_past H τ D b) le_rfl hp.1 _) ▸ h3 m' a b⟩
      rw [h1, U.SA_τ, strOf_τ_lt _ _ _ hm, strOf_τ_lt _ _ _ hm]
    · rintro ⟨hm, h1, h2, h3⟩
      refine ⟨hm, ?_, (rowsAt_past (U.SA_past H τ D hm) le_rfl hp.2 _).symm ▸ h2, fun m' a b =>
        (rowsAt_past (U.SA_past H τ D b) le_rfl hp.1 _).symm ▸ h3 m' a b⟩
      rw [h1, U.SA_τ, strOf_τ_lt _ _ _ hm, strOf_τ_lt _ _ _ hm]
  · unfold TabFor; rw [hφ]; simp only
    ext tr; simp only [Set.mem_setOf_eq, List.length_append, List.length_singleton]
    refine exists_congr fun m => ?_
    have hP := U.SA_snoc_past H τ D
    constructor
    · rintro ⟨hm, h1, h2, h3⟩
      refine ⟨hm, ?_, (rowsAt_past (m := m) hP (by omega) hp.2 _) ▸ h2, fun m' a b =>
        (rowsAt_past (m := m') hP (by omega) hp.1 _) ▸ h3 m' a b⟩
      rw [h1, ← (hP m (by omega)).1, applyLets_τ]
    · rintro ⟨hm, h1, h2, h3⟩
      refine ⟨hm, ?_, (rowsAt_past (m := m) hP (by omega) hp.2 _).symm ▸ h2, fun m' a b =>
        (rowsAt_past (m := m') hP (by omega) hp.1 _).symm ▸ h3 m' a b⟩
      rw [h1, ← (hP m (by omega)).1, applyLets_τ]

theorem tabFor_prev {d : LetDef Voc} {I : Interval} {φ : Formula Voc}
    (hφ : d.φ = .prev I φ) (hp : d.φ.PastF) :
    TabFor U.L.lets H d = {tr | ∃ m, m + 1 = H.length ∧ tr.1 = (U.SA H τ D).τ m ∧
        tr.2 ∈ RowsAt (U.SA H τ D) m φ d.xs} := by
  rw [hφ] at hp
  unfold TabFor; rw [hφ]; simp only
  ext tr; simp only [Set.mem_setOf_eq]
  refine exists_congr fun m => ?_
  constructor
  · rintro ⟨hm, h1, h2⟩
    refine ⟨hm, ?_, (rowsAt_past (U.SA_past H τ D (m := m) (by omega)) le_rfl (φ := φ) hp _) ▸ h2⟩
    rw [h1, U.SA_τ, strOf_τ_lt _ _ _ (by omega), strOf_τ_lt _ _ _ (by omega)]
  · rintro ⟨hm, h1, h2⟩
    refine ⟨hm, ?_, (rowsAt_past (U.SA_past H τ D (m := m) (by omega)) le_rfl (φ := φ) hp _).symm ▸ h2⟩
    rw [h1, U.SA_τ, strOf_τ_lt _ _ _ (by omega), strOf_τ_lt _ _ _ (by omega)]

end hist

/-- **`Eval` of a compiled let** is the let's semantics at the current time-point,
    provided the interpretation agrees with the semantics on the events the body
    mentions, and the table holds the content after the history (or, for a
    non-lagged table, after the history and the current time-point). -/
theorem eval_corr {d : LetDef Voc} {it : Item Voc} (hd : d ∈ U.L.lets)
    (hspec : LetItemSpec U.Ξ U.T.Γ U.colTy d it) (H : List (ℕ × DB Voc.toSignature)) (τ : ℕ)
    (D : DB Voc.toSignature) (h₀ : ∀ j, ∀ ev ∈ (strOf H τ D).D j, ¬ IsLet U.L.lets ev.e)
    (hmono : ∀ m ≤ H.length, (strOf H τ D).τ m ≤ τ)
    (R : Interpretation Voc) (T : Tables Voc)
    (hR : ∀ q ∈ d.φ.preds, R q = RelOf (U.SA H τ D) H.length q)
    (hT : T d.e = TabFor U.L.lets H d ∨
      ((∀ I φ, d.φ ≠ .prev I φ) ∧ T d.e = TabFor U.L.lets (H ++ [(τ, D)]) d)) :
    Eval it R T τ = RelOf (U.SA H τ D) H.length d.e := by
  rw [SA, U.relOf_let _ h₀ hd]
  rw [← SA]
  set S := U.SA H τ D
  set j := H.length
  have hb := U.lets_body d hd
  have hfvd := U.wf.fv_let d hd
  have hnd := U.wf.nodup_xs d hd
  have hcl := U.wf.clean.2 d hd
  have hp := U.pastF d hd
  have hSτ : S.τ j = τ := by rw [U.SA_τ, strOf_τ_len]
  have hSmono : ∀ m ≤ j, S.τ m ≤ S.τ j := fun m hm => by rw [hSτ, U.SA_τ]; exact hmono m hm
  have hpreds_strip : (stripExists d.φ).preds ⊆ d.φ.preds := by
    obtain ⟨ys, hys⟩ := exs_stripExists d.φ
    conv_rhs => rw [hys]
    clear hys; induction ys with
    | nil => exact le_rfl
    | cons y ys ih => exact ih
  cases hspec with
  | once I φ a hχ ha =>
    have hφ := letBody_since hb hχ
    have hfvφ : φ.fv = {x | x ∈ d.xs} := by rw [← hfvd, hφ]; simp [Formula.fv]
    have hRφ : ∀ q ∈ φ.preds, R q = RelOf S j q := fun q hq =>
      hR q (by rw [hφ]; exact Set.image_mono Set.subset_union_right hq)
    have hrows : rows R a d.xs = RowsAt S j φ d.xs := by
      rw [rows_guard ha le_rfl hRφ, hfvφ, rows_dom_eq hfvφ.le]
    simp only [Eval, Option.getD_some, letCols_names U.T.Γ]
    rw [hrows, hφ, ← hSτ]
    have := since_eval S j I .top φ d.xs (by simp [Formula.fv]) hfvφ.le (by rw [← hφ, hfvd])
      hSmono hnd (T d.e) (by
        rcases hT with h | ⟨-, h⟩
        · exact Or.inl (h.trans (U.tabFor_since H τ D hφ hp).1)
        · exact Or.inr (h.trans (U.tabFor_since H τ D hφ hp).2)) ∅
      (by ext r; simp [RowsAt, Formula.sat])
    simpa using this
  | prev I φ a hχ ha =>
    have hφ := letBody_prev hb hχ
    have hfvφ : φ.fv = {x | x ∈ d.xs} := by rw [← hfvd, hφ]; simp [Formula.fv]
    simp only [Eval, Option.getD_some]
    rw [hφ, ← hSτ]
    exact prev_eval S j I φ d.xs hfvφ.le (by rw [← hφ, hfvd]) hSmono hnd (T d.e) (by
      rcases hT with h | ⟨hn, -⟩
      · exact h.trans (U.tabFor_prev H τ D hφ hp)
      · exact absurd hφ (hn I φ))
  | agg ys ω ss gs φ a hχ hxs hnd' ha =>
    have hφ := letBody_agg hb hχ
    obtain ⟨π, ψ, hg, hc⟩ := ha
    have hsem : a.sem R = {v | v.dom = φ.fv ∧ φ.sat S v j} := by
      rw [clause_sem (N := φ.preds) (fun q hq => hR q (by rw [hφ]; exact hq))
        (GuardClause.preds_sub (a := a) hg) hc, trigSem_guards hg le_rfl]
    rw [hφ]
    exact agg_eval S j R T τ φ ys gs d.xs ω ss a none d.e _ hsem hxs hnd'
      (U.wf.agg_arity d hd ys ω ss gs φ hφ)
  | since I φl φr a r hχ hl ha hr =>
    have hφ := letBody_since hb hχ
    have hfvs : (Formula.since I φl φr).fv = {x | x ∈ d.xs} := by rw [← hφ, hfvd]
    have hfvl : φl.fv ⊆ {x | x ∈ d.xs} := by rw [← hfvs]; exact Set.subset_union_left
    have hfvr : φr.fv ⊆ {x | x ∈ d.xs} := by rw [← hfvs]; exact Set.subset_union_right
    have hX : ({x | x ∈ d.xs} ∪ (stripExists d.φ).fv : Set Voc.𝕍) = {x | x ∈ d.xs} := by
      rw [hχ, hfvs, Set.union_self]
    rw [hX] at ha hr
    have hpl : φl.preds ⊆ d.φ.preds := by
      rw [hφ]; exact Set.image_mono Set.subset_union_left
    have hpr : φr.preds ⊆ d.φ.preds := by
      rw [hφ]; exact Set.image_mono Set.subset_union_right
    have hrows : rows R a d.xs = RowsAt S j φr d.xs := by
      rw [rows_guard ha hfvr (fun q hq => hR q (hpr hq)), rows_dom_eq hfvr]
    have hrem : rows R r d.xs = RowsAt S j (.neg φl) d.xs := by
      rw [rows_guard hr hfvl (fun q hq => hR q (hpl hq)), rows_dom_eq (Φ := .neg φl) hfvl]
    simp only [Eval, Option.getD_some, letCols_names U.T.Γ]
    rw [hrows, hrem, hφ, ← hSτ]
    exact since_eval S j I φl φr d.xs hfvl hfvr hfvs hSmono hnd (T d.e) (by
      rcases hT with h | ⟨-, h⟩
      · exact Or.inl (h.trans (U.tabFor_since H τ D hφ hp).1)
      · exact Or.inr (h.trans (U.tabFor_since H τ D hφ hp).2)) _ rfl
  | filt f _ _ _ _ hf =>
    obtain ⟨ys, hys⟩ := exs_stripExists d.φ
    obtain ⟨h1, h2⟩ := filter_spec (N := (stripExists d.φ).preds)
      (fun q hq => hR q (hpreds_strip hq)) le_rfl hf
    simp only [Eval, letCols_names U.T.Γ, rows, Clause.sem, Val.proj]
    have : {r | ∃ v ∈ {v : Val Voc | v.dom = f.fv ∧ f.holds R v}, d.xs.mapM v = some r} =
        {r | ∃ v : Val Voc, v.dom = (stripExists d.φ).fv ∧ (stripExists d.φ).sat S v j ∧
          d.xs.mapM v = some r} := by
      ext r; simp only [Set.mem_setOf_eq, h1, h2]
      constructor
      · rintro ⟨v, ⟨a, b⟩, c⟩; exact ⟨v, a, b, c⟩
      · rintro ⟨v, a, b, c⟩; exact ⟨v, ⟨a, b⟩, c⟩
    rw [this]
    conv_rhs => rw [hys]
    rw [hys] at hfvd hcl
    exact present_rows S j hfvd hcl U.Ξ.zero
  | plet a _ _ _ _ ha =>
    obtain ⟨ys, hys⟩ := exs_stripExists d.φ
    have hxsχ : ({x | x ∈ d.xs} ∪ (stripExists d.φ).fv : Set Voc.𝕍) = (stripExists d.φ).fv := by
      have h1 := hfvd
      rw [hys, fv_exs] at h1
      refine Set.union_eq_right.2 fun x hx => ?_
      have : x ∈ ({x | x ∈ d.xs} : Set Voc.𝕍) := hx
      rw [← h1] at this; exact this.1
    rw [hxsχ] at ha
    simp only [Eval, letCols_names U.T.Γ]
    rw [rows_guard ha le_rfl (fun q hq => hR q (hpreds_strip hq))]
    conv_rhs => rw [hys]
    rw [hys] at hfvd hcl
    exact present_rows S j hfvd hcl U.Ξ.zero

end Setup

end Paper
