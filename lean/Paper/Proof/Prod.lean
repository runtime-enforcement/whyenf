/-
  Bounds on the values produced at one time-point.
-/
import Paper.Proof.Bind

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem toGArg_var {t : Term Voc} (h : (t.toGArg).isSome) {x : Voc.𝕍} (hx : x ∈ t.vars) :
    t = .var x := by
  cases t with
  | var y => simp [Term.vars] at hx; rw [hx]
  | const => simp [Term.vars] at hx
  | app => simp [Term.toGArg] at h

theorem exists_mem_varsList {x : Voc.𝕍} : ∀ {ts : List (Term Voc)}, x ∈ Term.varsList ts →
    ∃ t ∈ ts, x ∈ t.vars
  | [], h => by simp [Term.varsList] at h
  | t :: ts, h => by
    rcases h with h | h
    · exact ⟨t, by simp, h⟩
    · obtain ⟨t', h1, h2⟩ := exists_mem_varsList h; exact ⟨t', by simp [h1], h2⟩

theorem vars_sub_varsList {t : Term Voc} : ∀ {ts : List (Term Voc)}, t ∈ ts → t.vars ⊆ Term.varsList ts
  | [], h => by simp at h
  | t' :: ts, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Set.subset_union_left
    · exact (vars_sub_varsList h).trans Set.subset_union_right

theorem toClause_binds {π : GDisj Voc} {ψ : Formula Voc} {cl : Clause Voc} (h : toClause π ψ = some cl) :
    ∀ κ ∈ π, ∀ x ∈ κ.toFormula.fv, κ.Binds x := by
  intro κ hκ x hx
  rw [fv_gconj] at hx
  obtain ⟨γ, hγ, hx⟩ := hx
  unfold toClause at h
  split at h
  · simp at hκ; subst hκ; simp at hγ
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨g, hg, -⟩ := h
    simp only [GDisj.toEGuards, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨κs, hκs, -⟩ := hg
    obtain ⟨κ', -, hκκ'⟩ := forall₂_mem_left (mapM_forall₂ hκs) κ hκ
    simp only [bind, Option.bind_eq_some_iff] at hκκ'
    obtain ⟨as, has, -⟩ := hκκ'
    obtain ⟨a, -, hγa⟩ := forall₂_mem_left (mapM_forall₂ has) γ hγ
    cases γ with
    | pred q ts =>
      simp only [GAtom.toAtom, Option.map_eq_some_iff] at hγa
      obtain ⟨gs, hgs, -⟩ := hγa
      simp only [GAtom.toFormula, Formula.fv] at hx
      obtain ⟨t, ht, hxt⟩ := exists_mem_varsList hx
      obtain ⟨g', -, hg'⟩ := forall₂_mem_left (mapM_forall₂ hgs) t ht
      rw [toGArg_var (by simp [hg']) hxt] at ht
      exact ⟨_, hγ, Or.inl ⟨q, ts, rfl, ht⟩⟩
    | eq y c =>
      simp only [GAtom.toFormula, Formula.fv, Set.mem_singleton_iff] at hx
      subst hx; exact ⟨_, hγ, Or.inr ⟨c, rfl⟩⟩

namespace Setup
variable (U : Setup Voc)

/-- The enumerable events of `letItem` are base events or guarded lets. -/
theorem letM_GOk {q : Voc.ℰ} (hq : q ∈ letM U.Ξ U.T.Γ) : U.GOk q := by
  rcases hq with hq | hq
  · exact Or.inl fun ⟨d, hd, he⟩ => (U.wf.fresh_let d hd).2.2.1 (he ▸ hq)
  · exact Or.inr hq

/-- The input of one time-point, for termination. -/
structure TIn extends U.PtIn where
  C₀ : Set (REv Voc)
  hC₀ : U.Good C₀
  hDf : D.Finite
  hCf : C₀.Finite
  hTf : {d | ∃ q tr, tr ∈ TablesOf U.L.lets H q ∧ d ∈ tr.2}.Finite

namespace TIn
variable {U} (I : U.TIn)

/-- The base values. -/
def B : Set Voc.𝔻 :=
  {d | ∃ e ∈ I.D ∪ I.C₀, d ∈ e.2} ∪ {d | ∃ q tr, tr ∈ TablesOf U.L.lets I.H q ∧ d ∈ tr.2} ∪
    U.Consts ∪ U.Φ U.Consts

theorem B_finite : I.B.Finite := by
  refine ((Set.Finite.union ?_ I.hTf).union U.Consts_finite).union (U.Φ_finite U.Consts_finite)
  exact ((I.hDf.union I.hCf).biUnion fun e _ => List.finite_toSet e.2).subset
    fun d ⟨e, he, hd⟩ => Set.mem_biUnion he hd

/-- The bound at a position. -/
def WB (q : Pos Voc) : Set Voc.𝔻 := Wb U.O I.B U.Φ (U.Lv q)

theorem B_WB (q : Pos Voc) : I.B ⊆ I.WB q := Wb_base U.O I.B U.Φ _

theorem consts_WB (q : Pos Voc) : U.Consts ⊆ I.WB q :=
  fun d hd => I.B_WB q (Or.inl (Or.inr hd))

theorem WB_mono {q q' : Pos Voc} (h : DFG U.L.lets U.R q q') : I.WB q ⊆ I.WB q' :=
  Wb_mono U.O I.B U.Φ (U.Lv_mono h)

/-- The inputs below a position: the bound one level lower (or the constants). -/
def Low (q : Pos Voc) : Set Voc.𝔻 := if U.Lv q = 0 then U.Consts else Wb U.O I.B U.Φ (U.Lv q - 1)

theorem consts_Low (q : Pos Voc) : U.Consts ⊆ I.Low q := by
  unfold Low; split_ifs
  · exact le_rfl
  · exact fun d hd => Wb_base U.O I.B U.Φ _ (Or.inl (Or.inr hd))

theorem Φ_Low (q : Pos Voc) : U.Φ (I.Low q) ⊆ I.WB q := by
  unfold Low WB; split_ifs with h
  · rw [h]; exact fun d hd => Wb_base U.O I.B U.Φ 0 (Or.inr hd)
  · have : U.Lv q = U.Lv q - 1 + 1 := by omega
    rw [this]; exact Wb_Φ U.O I.B U.Φ _

theorem NS_Low {q q' : Pos Voc} (h : U.NS q q') : I.WB q ⊆ I.Low q' := by
  have hlt := U.Lv_strict h
  unfold Low WB; rw [if_neg (by omega)]
  exact Wb_mono U.O I.B U.Φ (by omega)

/-- Values of the events of the state are bounded. -/
def VB (y : Trip Voc) : Prop := ∀ e ∈ y.2.1 ∪ y.2.2, ∀ k (hk : k < e.2.length), e.2[k] ∈ I.WB (e.1, k)

/-- The rows of `q` are bounded. -/
def RelB (y : Trip Voc) (q : Voc.ℰ) : Prop :=
  ∀ r ∈ RelOf (I.St y) I.H.length q, ∀ k (hk : k < r.length), r[k] ∈ I.WB (q, k)

theorem relOf_base {y : Trip Voc} (hy : U.Good y.2.1) {q : Voc.ℰ} (hq : ¬ IsLet U.L.lets q) :
    RelOf (I.St y) I.H.length q = {r | (q, r) ∈ I.Xof y} := by
  have h₀ := U.good_noLet (I.good_X hy) I.H I.hH I.τ
  have hAL := applyLets_spec' U.L.lets U.wf.nodup U.scope_names _ h₀ U.L.lets.length le_rfl
  rw [List.take_length] at hAL
  obtain ⟨-, hbase, -⟩ := hAL
  ext r
  simp only [RelOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ev, hev, rfl, rfl⟩
    rw [PtIn.St, Setup.SA, hbase _ ev fun k hk _ he => hq ⟨_, List.getElem_mem hk, he.symm⟩,
      strOf_D_len] at hev
    exact hev
  · intro h
    refine ⟨⟨q, r, (I.good_X hy _ h).1⟩, ?_, rfl, rfl⟩
    rw [PtIn.St, Setup.SA, hbase _ _ fun k hk _ he => hq ⟨_, List.getElem_mem hk, he.symm⟩,
      strOf_D_len]
    exact h

theorem relB_base {y : Trip Voc} (hy : U.Good y.2.1) (hv : I.VB y) {q : Voc.ℰ}
    (hq : ¬ IsLet U.L.lets q) : I.RelB y q := by
  intro r hr k hk
  rw [I.relOf_base hy hq] at hr
  rcases hr with ⟨hD, -⟩ | hC
  · exact I.B_WB _ (Or.inl (Or.inl (Or.inl ⟨_, Or.inl hD, List.getElem_mem hk⟩)))
  · exact hv _ (Or.inl hC) k hk

/-- A variable bound by a satisfied guard is bounded at its binding position. -/
theorem bind_bound {y : Trip Voc} {κ : GConj Voc} {v : Val Voc}
    (hs : κ.toFormula.sat (I.St y) v I.H.length) {x : Voc.𝕍} (hb : κ.Binds x)
    (hRB : ∀ q ts, GAtom.pred q ts ∈ κ → I.RelB y q) :
    (∃ q ts k a, GAtom.pred q ts ∈ κ ∧ ts[k]? = some (Term.var x) ∧ v x = some a ∧
      a ∈ I.WB (q, k)) ∨ (∃ c, GAtom.eq x c ∈ κ ∧ v x = some c) := by
  rcases bind_atom hs hb with ⟨q, ts, k, hq, hk, args, hargs, a, ha, hva⟩ | h
  · obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.1 ha
    exact Or.inl ⟨q, ts, k, _, hq, hk, hva, hRB q ts hq args hargs k hk'⟩
  · exact Or.inr h

theorem kappa_fv {m : Set Voc.ℰ} {X : Set Voc.𝕍} {Φ : Formula Voc} {π : GDisj Voc} {ψ : Formula Voc}
    (h : Guards m X Φ = some (π, ψ)) (hX : Φ.fv ⊆ X) : ∀ κ ∈ π, κ.toFormula.fv = X := by
  have hg := Guards_spec h
  obtain ⟨hb, -⟩ := lemma_4_2 h
  intro κ hκ
  exact le_antisymm ((hg.fv_sub κ hκ).trans hX) fun x hx => Binds.mem_fv (hb κ hκ x hx)

/-- **Values of compiled let guards.** -/
theorem guard_val {y : Trip Voc} {m : Set Voc.ℰ} {X : Set Voc.𝕍} {Φ : Formula Voc}
    {π : GDisj Voc} {ψ : Formula Voc} (ha : Guards m X Φ = some (π, ψ)) (hX : Φ.fv ⊆ X)
    (hRB : ∀ q ∈ m, q ∈ Φ.preds → I.RelB y q) {v : Val Voc}
    (hv : v ∈ TrigSem (I.St y) I.H.length π ψ)
    {x : Voc.𝕍} (hx : x ∈ X) :
    (∃ q ts k a, (q, ts) ∈ Φ.atoms ∧ q ∈ m ∧ ts[k]? = some (Term.var x) ∧ v x = some a ∧
      a ∈ I.WB (q, k)) ∨ (∃ c ∈ Φ.eqConsts, v x = some c) := by
  have hg := Guards_spec ha
  obtain ⟨hb, -⟩ := lemma_4_2 ha
  have hκX := kappa_fv ha hX
  by_cases hπ : π = [[]]
  · have : X = ∅ := by rw [← hκX [] (by rw [hπ]; simp)]; simp [GConj.toFormula, Formula.fv]
    rw [this] at hx; exact absurd hx (Set.notMem_empty _)
  · rw [trigSem_ne _ _ hπ] at hv
    obtain ⟨⟨κ, hκ, -, hs⟩, -⟩ := hv
    rcases I.bind_bound hs (hb κ hκ x hx) (fun q ts hq => hRB q (hg.names κ hκ q ts hq)
        ⟨(q, ts), hg.atoms_sub.1 (atom_mem_disj hκ hq), rfl⟩) with
      ⟨q, ts, k, a, hq, hk, hva, ha'⟩ | ⟨c, hc, hvc⟩
    · exact Or.inl ⟨q, ts, k, a, hg.atoms_sub.1 (atom_mem_disj hκ hq), hg.names κ hκ q ts hq, hk,
        hva, ha'⟩
    · exact Or.inr ⟨c, hg.eqs κ hκ x c hc, hvc⟩

theorem dom_trigSem {y : Trip Voc} {m : Set Voc.ℰ} {X : Set Voc.𝕍} {Φ : Formula Voc}
    {π : GDisj Voc} {ψ : Formula Voc} (ha : Guards m X Φ = some (π, ψ)) (hX : Φ.fv ⊆ X)
    {v : Val Voc} (hv : v ∈ TrigSem (I.St y) I.H.length π ψ) : v.dom = X := by
  rw [trigSem_guards ha hX] at hv; exact hv.1

/-- The rows of a compiled let guard are bounded. -/
theorem guard_rows {y : Trip Voc} {d : LetDef Voc} (hd : d ∈ U.L.lets) {X : Set Voc.𝕍}
    {Φ : Formula Voc} {a : Clause Voc} (ha : GuardClause (letM U.Ξ U.T.Γ) X Φ a) (hX : Φ.fv ⊆ X)
    (hat : Φ.atoms ⊆ d.φ.atoms) (heq : Φ.eqConsts ⊆ d.φ.eqConsts)
    (hRB : ∀ q ∈ letM U.Ξ U.T.Γ, q ∈ Φ.preds → I.RelB y q) :
    ∀ r ∈ rows (fun q => RelOf (I.St y) I.H.length q) a d.xs, ∀ i (hi : i < r.length),
      r[i] ∈ I.WB (d.e, i) := by
  obtain ⟨π, ψ, hg, hc⟩ := ha
  have hsem := clause_sem (N := Set.univ) (R := fun q => RelOf (I.St y) I.H.length q)
    (fun q _ => rfl) (Set.subset_univ _) hc
  rintro r ⟨v, hv, hr⟩ i hi
  rw [hsem] at hv
  rw [Val.proj, mapM_eq_some] at hr
  have hlen := len_of_map hr
  have hxi : v (d.xs[i]'(hlen ▸ hi)) = some r[i] := by
    have := congrArg (fun l => l[i]?) hr
    simp only [List.getElem?_map] at this
    rw [List.getElem?_eq_getElem (hlen ▸ hi), List.getElem?_eq_getElem hi] at this
    simpa using this
  have hdom := I.dom_trigSem hg hX hv
  have hxX : (d.xs[i]'(hlen ▸ hi)) ∈ X := by
    rw [← hdom]; show (v (d.xs[i]'(hlen ▸ hi))).isSome; rw [hxi]; rfl
  rcases I.guard_val hg hX hRB hv hxX with ⟨q, ts, k, a', hq, -, hk, hva, ha'⟩ | ⟨c, hc', hvc⟩
  · rw [hxi] at hva; cases hva
    refine I.WB_mono (Or.inr ⟨d, hd, rfl, _, ?_, ts, hat hq, _, hk, Or.inl rfl⟩) ha'
    exact List.getElem?_eq_getElem (hlen ▸ hi)
  · rw [hxi] at hvc; cases hvc
    exact I.consts_WB _ (Or.inr (Set.mem_biUnion (s := {dl | dl ∈ U.L.lets}) hd (heq hc')))

theorem window_vals {T : Tables Voc} (hT : T = TablesOf U.L.lets I.H) {p : Voc.ℰ} {τ n : ℕ}
    {b : ℕ∞} {r : List Voc.𝔻} (h : r ∈ window (T p) τ n b) {i : ℕ} (hi : i < r.length) :
    r[i] ∈ I.B := by
  obtain ⟨τ', h1, -⟩ := h
  subst hT
  exact Or.inl (Or.inl (Or.inr ⟨p, (τ', r), h1, List.getElem_mem hi⟩))

theorem atoms_strip (φ : Formula Voc) : (stripExists φ).atoms ⊆ φ.atoms ∧
    (stripExists φ).eqConsts ⊆ φ.eqConsts ∧ (stripExists φ).preds ⊆ φ.preds := by
  induction φ with
  | ex x φ ih => exact ih
  | _ => exact ⟨le_rfl, le_rfl, le_rfl⟩

/-- **The rows of the guarded lets are bounded.** -/
theorem rel_let {y : Trip Voc} (hy : U.Good y.2.1) (hv : I.VB y) :
    ∀ k (hk : k < U.L.lets.length), U.GOk U.L.lets[k].e →
      (∀ q, q ∈ U.L.lets[k].φ.preds → U.GOk q → I.RelB y q) → I.RelB y U.L.lets[k].e := by
  intro k hk hok hRB
  set d := U.L.lets[k] with hdk
  have hd : d ∈ U.L.lets := List.getElem_mem hk
  obtain ⟨its, hits⟩ := U.items
  obtain ⟨it, hit, hspec⟩ := forall₂_mem_left hits d hd
  set R : Interpretation Voc := fun q => RelOf (I.St y) I.H.length q
  have hcorr := U.eval_corr hd hspec I.H I.τ (REv.toDB (I.Xof y))
    (U.good_noLet (I.good_X hy) I.H I.hH I.τ) (fun m hm => by
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · rw [strOf_τ_lt _ _ _ hm]; exact I.hmono m hm
      · rw [strOf_τ_len]) R (TablesOf U.L.lets I.H) (fun _ _ => rfl)
    (Or.inl (U.tablesOf_let _ hd))
  intro r hr
  change r ∈ RelOf (U.SA I.H I.τ (REv.toDB (I.Xof y))) I.H.length d.e at hr
  rw [← hcorr] at hr
  have hm : ∀ Φ : Formula Voc, Φ.preds ⊆ d.φ.preds → ∀ q ∈ letM U.Ξ U.T.Γ, q ∈ Φ.preds → I.RelB y q :=
    fun Φ hΦ q hq hqΦ => hRB q (hΦ hqΦ) (U.letM_GOk hq)
  have hb := U.lets_body d hd
  cases hspec with
  | once J φ a hχ ha =>
    have hφ := letBody_since hb hχ
    have hfvφ : φ.fv ⊆ {x | x ∈ d.xs} := by
      rw [← U.wf.fv_let d hd, hφ]; exact Set.subset_union_right
    have hsub : φ.atoms ⊆ d.φ.atoms := by rw [hφ]; exact Set.subset_union_right
    have hsubq : φ.eqConsts ⊆ d.φ.eqConsts := by rw [hφ]; exact Set.subset_union_right
    simp only [Eval, Option.getD_some, letCols_names U.T.Γ] at hr
    intro i hi
    rcases hr with ⟨hw, -⟩ | hr
    · exact I.B_WB _ (I.window_vals rfl hw hi)
    · split_ifs at hr
      · exact I.guard_rows hd ha le_rfl hsub hsubq (hm φ (Set.image_mono hsub)) r hr i hi
      · exact absurd hr (Set.notMem_empty _)
  | since J φl φr a r' hχ _ ha hr' =>
    have hφ := letBody_since hb hχ
    have hX : (stripExists d.φ).fv ⊆ ({x | x ∈ d.xs} ∪ (stripExists d.φ).fv) := Set.subset_union_right
    have hsub : φr.atoms ⊆ d.φ.atoms := by rw [hφ]; exact Set.subset_union_right
    have hsubq : φr.eqConsts ⊆ d.φ.eqConsts := by rw [hφ]; exact Set.subset_union_right
    have hfvr : φr.fv ⊆ ({x | x ∈ d.xs} ∪ (stripExists d.φ).fv) := by
      rw [hχ]; exact Set.subset_union_right.trans Set.subset_union_right
    simp only [Eval, Option.getD_some, letCols_names U.T.Γ] at hr
    intro i hi
    rcases hr with ⟨hw, -⟩ | hr
    · exact I.B_WB _ (I.window_vals rfl hw hi)
    · split_ifs at hr
      · exact I.guard_rows hd ha hfvr hsub hsubq (hm φr (Set.image_mono hsub)) r hr i hi
      · exact absurd hr (Set.notMem_empty _)
  | prev J φ a hχ ha =>
    simp only [Eval, Option.getD_some] at hr
    intro i hi
    exact I.B_WB _ (I.window_vals rfl hr hi)
  | plet a _ _ _ _ ha =>
    obtain ⟨h1, h2, h3⟩ := atoms_strip d.φ
    simp only [Eval, letCols_names U.T.Γ] at hr
    exact I.guard_rows hd ha Set.subset_union_right h1 h2 (hm _ h3) r hr
  | filt f _ _ _ hΓ _ =>
    exfalso
    obtain ⟨c, s, hΓ⟩ := hΓ
    rcases hok with hn | ⟨c', s', h'⟩
    · exact hn ⟨d, hd, rfl⟩
    · rw [hΓ] at h'; simp at h'
  | agg ys ω ss gs φ a hχ hxs hnd ha =>
    have hφ := letBody_agg hb hχ
    obtain ⟨π, ψ, hg, hc⟩ := ha
    have hsem := clause_sem (N := Set.univ) (R := R) (fun q _ => rfl) (Set.subset_univ _) hc
    have hRBφ := hm φ (by rw [hφ]; exact le_rfl)
    have heqφ : φ.eqConsts ⊆ d.φ.eqConsts := by rw [hφ]; exact le_rfl
    have hatφ : φ.atoms ⊆ d.φ.atoms := by rw [hφ]; exact le_rfl
    have hconst : ∀ c ∈ φ.eqConsts, c ∈ U.Consts :=
      fun c hc' => Or.inr (Set.mem_biUnion (s := {dl | dl ∈ U.L.lets}) hd (heqφ hc'))
    simp only [Eval] at hr
    obtain ⟨vb, hvb, gv, hgv, hfin, M, hM, w, hw, rfl⟩ := hr
    rw [hsem] at hvb
    rw [Val.proj, mapM_eq_some] at hgv
    have hlg := len_of_map hgv
    intro i hi
    by_cases hig : i < gv.length
    · rw [List.getElem_append_left hig]
      have hxi : vb (gs[i]'(hlg ▸ hig)) = some gv[i] := by
        have := congrArg (fun l => l[i]?) hgv
        simp only [List.getElem?_map] at this
        rw [List.getElem?_eq_getElem (hlg ▸ hig), List.getElem?_eq_getElem hig] at this
        simpa using this
      have hdom := I.dom_trigSem hg le_rfl hvb
      have hxX : (gs[i]'(hlg ▸ hig)) ∈ φ.fv := by
        rw [← hdom]; show (vb _).isSome; rw [hxi]; rfl
      have hxs_i : d.xs[i]? = some (gs[i]'(hlg ▸ hig)) := by
        rw [hxs, List.getElem?_append_left (hlg ▸ hig)]; exact List.getElem?_eq_getElem _
      rcases I.guard_val hg le_rfl hRBφ hvb hxX with ⟨q, ts, k', a', hq, -, hk, hva, ha'⟩ |
          ⟨c, hc', hvc⟩
      · rw [hxi] at hva; cases hva
        exact I.WB_mono (Or.inr ⟨d, hd, rfl, _, hxs_i, ts, hatφ hq, _, hk, Or.inl rfl⟩) ha'
      · rw [hxi] at hvc; cases hvc
        exact I.consts_WB _ (hconst _ hc')
    · push Not at hig
      have hiw : i - gv.length < (List.ofFn w).length := by simp at hi ⊢; omega
      rw [List.getElem_append_right hig]
      -- the result column
      have hlen' : gs.length ≤ i := hlg ▸ hig
      have hiys : i - gs.length < ys.length := by
        have := U.wf.agg_arity d hd ys ω ss gs φ hφ; simp at hi; omega
      have hxs_i : d.xs[i]? = some (ys[i - gs.length]'hiys) := by
        rw [hxs, List.getElem?_append_right hlen']; exact List.getElem?_eq_getElem _
      have hagg : AggResult U.L.lets (d.e, i) :=
        ⟨d, hd, rfl, ys, ω, ss, gs, φ, hφ, _, List.getElem_mem hiys, hxs_i⟩
      refine I.Φ_Low _ (Or.inr ⟨d, hd, ys, ω, ss, gs, φ, hφ, hfin.toFinset, ?_, M, hM, w, hw,
        List.getElem_mem _⟩)
      intro v hv
      rw [Set.Finite.coe_toFinset] at hv
      obtain ⟨hv1, -⟩ := hv
      rw [hsem] at hv1
      have hdom := I.dom_trigSem hg le_rfl hv1
      refine ⟨hdom, fun x hx => ?_⟩
      rcases I.guard_val hg le_rfl hRBφ hv1 hx with ⟨q, ts, k', a', hq, -, hk, hva, ha'⟩ |
          ⟨c, hc', hvc⟩
      · refine ⟨a', I.NS_Low (Or.inr ⟨⟨d, hd, rfl, _, hxs_i, ts, hatφ hq, x, hk,
          Or.inr ⟨ys, ω, ss, gs, φ, hφ, List.getElem_mem hiys⟩⟩, Or.inr hagg⟩) ha', hva⟩
      · exact ⟨c, I.consts_Low _ (hconst c hc'), hvc⟩

/-- **All guard-capable relations are bounded.** -/
theorem rel_all {y : Trip Voc} (hy : U.Good y.2.1) (hv : I.VB y) : ∀ q, U.GOk q → I.RelB y q := by
  have key : ∀ k (hk : k < U.L.lets.length), U.GOk U.L.lets[k].e → I.RelB y U.L.lets[k].e := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hok
      refine I.rel_let hy hv k hk hok fun q hq hokq => ?_
      rcases U.scope_names k hk q (by
          rwa [Formula.names_eq_preds (IsLetBody.noLet (U.lets_body _ (List.getElem_mem hk)))])
        with hq' | ⟨k', hk', hk'l, rfl⟩
      · exact I.relB_base hy hv hq'
      · exact ih k' hk' hk'l hokq
  intro q hq
  by_cases hl : IsLet U.L.lets q
  · obtain ⟨d, hd, rfl⟩ := hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    exact key k hk hq
  · exact I.relB_base hy hv hl

/-- **The effects of a firing are bounded.** -/
theorem rule_bound {y : Trip Voc} (hy : U.Good y.2.1) (hv : I.VB y) {c : EClause Voc} (hc : c ∈ U.R)
    {v : Val Voc} (hvt : v ∈ TrigSem (I.St y) I.H.length c.π c.ψ) {a : List Voc.𝔻}
    (ha : Term.evalList v c.ε.args = some a) : ∀ k (hk : k < a.length), a[k] ∈ I.WB (c.ε.name, k) := by
  intro k hk
  have hlen := evalList_length ha
  obtain ⟨t, htk⟩ : ∃ t, c.ε.args[k]? = some t := ⟨_, List.getElem?_eq_getElem (hlen ▸ hk)⟩
  obtain ⟨d, hd, hdt⟩ := evalList_get ha htk
  rw [List.getElem?_eq_getElem hk] at hd; cases hd
  have htm : t ∈ c.ε.args := List.mem_of_getElem? htk
  have hg := (U.R_props c hc).2
  obtain ⟨it, -⟩ : ∃ it, True := ⟨(), trivial⟩
  -- the clause is compiled
  have hcomp : ∃ cl, toClause c.π c.ψ = some cl := by
    obtain ⟨rules, -, hrules, -⟩ := U.prog_spec
    obtain ⟨p, -, hp⟩ := forall₂_mem_left hrules c ((U.hrs c).2 hc |> List.mem_mergeSort.2)
    exact hp.2.toClause
  obtain ⟨cl, hcl⟩ := hcomp
  have htvars : t.vars ⊆ Term.varsList c.ε.args := vars_sub_varsList htm
  have htc : t.consts ⊆ U.Consts := by
    intro x hx
    exact Or.inl (Set.mem_biUnion hc (Or.inr (Set.mem_biUnion (s := {t | t ∈ c.ε.args}) htm hx)))
  -- where the values of the variables of `t` come from
  have hbind : ∀ x ∈ t.vars,
      (∃ q k' a', DFGEdge U.R c t (q, k') (c.ε.name, k) ∧ v x = some a' ∧ a' ∈ I.WB (q, k')) ∨
      (∃ c' ∈ U.Consts, v x = some c') := by
    intro x hx
    by_cases hπ : c.π = [[]]
    · have := hg [] (by rw [hπ]; simp)
      simp [GConj.toFormula, Formula.fv] at this
      have h2 := htvars hx; rw [this.2] at h2; exact absurd h2 (Set.notMem_empty _)
    · rw [trigSem_ne _ _ hπ] at hvt
      obtain ⟨⟨κ, hκ, -, hs⟩, -⟩ := hvt
      have hxκ : x ∈ κ.toFormula.fv := hg κ hκ (Or.inr (htvars hx))
      rcases I.bind_bound hs (toClause_binds hcl κ hκ x hxκ) (fun q ts hq =>
          I.rel_all hy hv q (U.R_gnames c hc κ hκ q ts hq)) with
        ⟨q, ts, k', a', hq, hk', hva, ha'⟩ | ⟨c', hc', hvc⟩
      · exact Or.inl ⟨q, k', a', ⟨hc, x, ⟨ts, Or.inl ⟨κ, hκ, hq⟩, hk'⟩, rfl, htk, hx⟩, hva, ha'⟩
      · refine Or.inr ⟨c', Or.inl (Set.mem_biUnion hc (Or.inl ?_)), hvc⟩
        simp only [EClause.trig, Formula.eqConsts]; exact Or.inl (eq_mem_disj hκ hc')
  by_cases hst : ∀ f ∈ t.funs, Stable U.O f
  · rcases stable_eval U.O v t hst _ hdt with ⟨x, hx, b, hb, hdb⟩ | ⟨c', hc', hdc⟩
    · have hbW : b ∈ I.WB (c.ε.name, k) := by
        rcases hbind x hx with ⟨q, k', a', he, hva, ha'⟩ | ⟨c', hc', hvc⟩
        · rw [hb] at hva; cases hva; exact I.WB_mono (Or.inl ⟨c, t, he⟩) ha'
        · rw [hb] at hvc; cases hvc; exact I.consts_WB _ hc'
      rcases hdb with rfl | h
      · exact hbW
      · exact Wb_down U.O I.B U.Φ hbW h
    · have hcW := I.consts_WB (c.ε.name, k) (htc hc')
      rcases hdc with rfl | h
      · exact hcW
      · exact Wb_down U.O I.B U.Φ hcW h
  · have hrest : v.restrict t.vars ∈ ValsIn t.vars (I.Low (c.ε.name, k)) := by
      refine ⟨Val.restrict_dom fun x hx => ?_, fun x hx => ?_⟩
      · rcases hbind x hx with ⟨q, k', a', -, hva, -⟩ | ⟨c', -, hvc⟩
        · rw [hva]; rfl
        · rw [hvc]; rfl
      · rw [Val.restrict_agree v _ x hx]
        rcases hbind x hx with ⟨q, k', a', he, hva, ha'⟩ | ⟨c', hc', hvc⟩
        · exact ⟨a', I.NS_Low (Or.inl ⟨c, t, he, fun h => hst h.2.2⟩) ha', hva⟩
        · exact ⟨c', I.consts_Low _ hc', hvc⟩
    refine I.Φ_Low _ (Or.inl ⟨c, hc, t, htm, _, hrest, ?_⟩)
    rw [Term.eval_congr (v.restrict t.vars) v t fun x hx => Val.restrict_agree v _ x hx]
    exact hdt

end TIn

end Setup

end Paper
