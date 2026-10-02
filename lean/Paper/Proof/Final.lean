/-
  The MFOTL part of the proof of Theorem 4.3: if every clause of `R` is
  satisfied on the output, the obligation events mean what they should and
  the let-normal form holds.
-/
import Paper.Proof.Lets

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-! ## The realization closure -/

theorem realization_structure {Ξ : RwSetting Voc} {T : Typed Voc} {C R : Set (EClause Voc)}
    (hR : R ∈ Realizations Ξ T C) :
    C ⊆ R ∧ (∀ c ∈ R, ∀ p, c.ε.name = Ξ.cauN p → ∃ f ∈ T.CC p, f ⊆ R) ∧
      (∀ c ∈ R, ∀ p, c.ε.name = Ξ.supN p → ∃ g ∈ T.CS p, g ⊆ R) ∧
      ∀ c ∈ R, c ∈ C ∨ (∃ p, ∃ f ∈ T.CC p, c ∈ f) ∨ (∃ p, ∃ g ∈ T.CS p, c ∈ g) := by
  obtain ⟨f, g, ⟨hC, hcl⟩, hmin⟩ := hR
  refine ⟨hC, fun c hc p hp => ⟨f p, (hcl c hc p).1 hp⟩, fun c hc p hp => ⟨g p, (hcl c hc p).2 hp⟩, ?_⟩
  let U : Set (EClause Voc) := C ∪ {c | ∃ p, (∃ c' ∈ R, c'.ε.name = Ξ.cauN p) ∧ c ∈ f p} ∪
    {c | ∃ p, (∃ c' ∈ R, c'.ε.name = Ξ.supN p) ∧ c ∈ g p}
  have hUR : U ⊆ R := by
    rintro c ((hc | ⟨p, ⟨c', hc', hp⟩, hc⟩) | ⟨p, ⟨c', hc', hp⟩, hc⟩)
    · exact hC hc
    · exact ((hcl c' hc' p).1 hp).2 hc
    · exact ((hcl c' hc' p).2 hp).2 hc
  have hU : C ⊆ U ∧ ∀ c ∈ U, ∀ p,
      (c.ε.name = Ξ.cauN p → f p ∈ T.CC p ∧ f p ⊆ U) ∧
      (c.ε.name = Ξ.supN p → g p ∈ T.CS p ∧ g p ⊆ U) := by
    refine ⟨fun c hc => Or.inl (Or.inl hc), fun c hc p => ⟨fun hp => ?_, fun hp => ?_⟩⟩
    · exact ⟨((hcl c (hUR hc) p).1 hp).1, fun c'' h => Or.inl (Or.inr ⟨p, ⟨c, hUR hc, hp⟩, h⟩)⟩
    · exact ⟨((hcl c (hUR hc) p).2 hp).1, fun c'' h => Or.inr ⟨p, ⟨c, hUR hc, hp⟩, h⟩⟩
  intro c hc
  rcases hmin U hU hc with (hc | ⟨p, ⟨c', hc', hp⟩, hc⟩) | ⟨p, ⟨c', hc', hp⟩, hc⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨p, f p, ((hcl c' hc' p).1 hp).1, hc⟩)
  · exact Or.inr (Or.inr ⟨p, g p, ((hcl c' hc' p).2 hp).1, hc⟩)

/-! ## Valuations from tuples -/

theorem val_of_args : ∀ (xs : List Voc.𝕍) (args : List Voc.𝔻), xs.Nodup → xs.length = args.length →
    ∃ v : Val Voc, xs.map v = args.map some ∧ ∀ y, (v y).isSome ↔ y ∈ xs
  | [], [], _, _ => ⟨fun _ => none, rfl, by simp⟩
  | x :: xs, a :: args, hnd, hl => by
    obtain ⟨v, hv, hdom⟩ := val_of_args xs args (List.nodup_cons.1 hnd).2 (by simpa using hl)
    have hx : x ∉ xs := (List.nodup_cons.1 hnd).1
    refine ⟨v.upd x a, ?_, fun y => ?_⟩
    · simp only [List.map_cons, Val.upd_same, List.cons.injEq, true_and]
      rw [← hv]; refine List.map_congr_left fun y hy => ?_
      exact Val.upd_ne _ _ (fun h => hx (h ▸ hy))
    · by_cases hyx : y = x
      · subst hyx; simp
      · rw [Val.upd_ne _ _ hyx, hdom]; simp [hyx]
  | [], _ :: _, _, hl | _ :: _, [], _, hl => by simp at hl

theorem Clean_bigAnd_of {G : Set Voc.𝕍} :
    ∀ {φs : List (Formula Voc)}, (∀ φ ∈ φs, φ.Clean G ∧ φ.fv = ∅) → (bigAnd φs).Clean G
  | [], _ => trivial
  | [φ], h => (h φ (by simp)).1
  | φ :: ψ :: φs, h => by
    rw [show bigAnd (φ :: ψ :: φs) = .and φ (bigAnd (ψ :: φs)) from rfl]
    have hrest : ∀ χ ∈ ψ :: φs, χ.Clean G ∧ χ.fv = ∅ := fun χ hχ => h χ (by simp [hχ])
    have hfv : (bigAnd (ψ :: φs)).fv = ∅ := by
      rw [fv_bigAnd]; ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨χ, hχ, hx⟩; rw [(hrest χ hχ).2] at hx; exact hx
    refine ⟨?_, ?_⟩
    · rw [hfv, Set.union_empty]; exact (h φ (by simp)).1
    · rw [(h φ (by simp)).2, Set.union_empty]; exact Clean_bigAnd_of hrest

/-! ## Gated guards -/

theorem sat_gate_disj (S : Str Voc.toSignature) (w : Val Voc) (i : ℕ) (γ : GAtom Voc) (π : GDisj Voc) :
    (GDisj.toFormula (π.map (· ++ [γ]))).sat S w i ↔ π.toFormula.sat S w i ∧ γ.toFormula.sat S w i := by
  simp only [sat_disj, sat_conj, List.mem_map]
  constructor
  · rintro ⟨_, ⟨κ, hκ, rfl⟩, h⟩
    exact ⟨⟨κ, hκ, fun a ha => h a (List.mem_append_left _ ha)⟩, h γ (by simp)⟩
  · rintro ⟨⟨κ, hκ, h⟩, hγ⟩
    refine ⟨_, ⟨κ, hκ, rfl⟩, fun a ha => ?_⟩
    rcases List.mem_append.1 ha with ha | ha
    · exact h a ha
    · simp at ha; subst ha; exact hγ

theorem fv_gate_disj (γ : GAtom Voc) (π : GDisj Voc) :
    (GDisj.toFormula (π.map (· ++ [γ]))).fv ⊆ π.toFormula.fv ∪ γ.toFormula.fv := by
  rw [fv_gdisj, fv_gdisj]
  rintro y ⟨_, hκ, hy⟩
  simp only [List.mem_map] at hκ
  obtain ⟨κ, hκ, rfl⟩ := hκ
  rw [fv_gconj] at hy
  obtain ⟨a, ha, hy⟩ := hy
  rcases List.mem_append.1 ha with ha | ha
  · exact Or.inl ⟨κ, hκ, by rw [fv_gconj]; exact ⟨a, ha, hy⟩⟩
  · simp at ha; subst ha; exact Or.inr hy

theorem varsList_map_var' (xs : List Voc.𝕍) : Term.varsList (xs.map Term.var) = {y | y ∈ xs} := by
  induction xs with
  | nil => simp [Term.varsList]
  | cons x xs ih => simp only [List.map_cons, Term.varsList, Term.vars, ih]; ext y; simp

theorem covers_of_map {w : Val Voc} {xs : List Voc.𝕍} {A : List Voc.𝔻} (h : xs.map w = A.map some) :
    w.Covers {y | y ∈ xs} := by
  intro y hy
  have : w y ∈ A.map some := h ▸ List.mem_map_of_mem hy
  obtain ⟨a, -, ha⟩ := List.mem_map.1 this
  rw [← ha]; rfl

/-- A clause gated by `q(x̄)`, with `q(Ā)` present, holds under `x̄ = Ā`. -/
theorem satRel_gate {S : Str Voc.toSignature} {dl : ℕ → ℕ} {q : Voc.ℰ} {xs : List Voc.𝕍}
    {A : List Voc.𝔻} {i : ℕ} {c : EClause Voc}
    (hsat : SatRel S dl (fun _ => True) ⟨c.π.map (· ++ [.pred q (xs.map Term.var)]), c.ψ, c.ε⟩ i)
    (hq : ∃ ev ∈ S.D i, ev.e = q ∧ ev.args = A) :
    SatRel S dl (fun w => xs.map w = A.map some) c i := by
  intro w hw hΘ htr
  have hγ : (GAtom.toFormula (.pred q (xs.map Term.var))).sat S w i := by
    obtain ⟨ev, hev, he, ha⟩ := hq
    refine ⟨A, ?_, ev, hev, he, ha⟩
    rw [evalList_map_var, mapM_eq_some]; exact hΘ
  refine hsat w ?_ trivial ?_
  · simp only [EClause.vars, EClause.trig, Formula.fv] at hw ⊢
    intro y hy
    rcases hy with (hy | hy) | hy
    · rcases fv_gate_disj _ _ hy with hy | hy
      · exact hw y (Or.inl (Or.inl hy))
      · simp only [GAtom.toFormula, Formula.fv, varsList_map_var'] at hy
        exact covers_of_map hΘ y hy
    · exact hw y (Or.inl (Or.inr hy))
    · exact hw y (Or.inr hy)
  · simp only [EClause.trig, Formula.sat, sat_gate_disj] at htr ⊢
    exact ⟨⟨htr.1, hγ⟩, htr.2⟩

theorem dep_map (xs : List Voc.𝕍) (A : List Voc.𝔻) :
    DepOn (fun w : Val Voc => xs.map w = A.map some) {y | y ∈ xs} := by
  intro w w' hw; simp only; rw [List.map_congr_left fun y hy => hw y hy]

/-! ## The setting -/

/-- Everything the MFOTL part of the proof needs. -/
structure FinalSetting (Voc : Vocabulary) where
  Ξ : RwSetting Voc
  φ : Formula Voc
  L : LNF Voc
  valid : L.Valid
  wf : WF Ξ φ L
  T : Typed Voc
  hT : TypeLets Ξ L.lets = some T
  𝒞 : CSet Voc
  hrw : Rw Ξ T.Γ .C (bigAnd L.chis) 𝒞
  C : Set (EClause Voc)
  hC : C ∈ 𝒞
  R : Set (EClause Voc)
  hR : R ∈ Realizations Ξ T C

namespace FinalSetting
variable (F : FinalSetting Voc)

theorem lets_body : ∀ d ∈ F.L.lets, d.φ.IsLetBody := F.valid.1

theorem scope_names : ∀ k (hk : k < F.L.lets.length), ∀ e ∈ F.L.lets[k].φ.names,
    ¬ IsLet F.L.lets e ∨ ∃ k' < k, ∃ hk' : k' < F.L.lets.length, F.L.lets[k'].e = e := by
  intro k hk e he
  rw [Formula.names_eq_preds (IsLetBody.noLet (F.lets_body _ (List.getElem_mem hk)))] at he
  exact F.wf.scope k hk e he

/-- The obligation events of the first `k` lets are sound. -/
def OblUpTo (S : Str Voc.toSignature) (k : ℕ) : Prop :=
  ∀ k' (hk' : k' < F.L.lets.length), k' < k → ∀ i (ev : Event Voc.toSignature), ev ∈ S.D i →
    (ev.e = F.Ξ.cauN F.L.lets[k'].e → ∃ ev' ∈ S.D i, ev'.e = F.L.lets[k'].e ∧ ev'.args = ev.args) ∧
    (ev.e = F.Ξ.supN F.L.lets[k'].e → ∀ ev' ∈ S.D i, ev'.e = F.L.lets[k'].e → ev'.args ≠ ev.args)

theorem oblSem_of_upTo {S : Str Voc.toSignature} {k : ℕ} (h : F.OblUpTo S k) {Γ : LetCtx Voc}
    (hΓ : ∀ e, (Γ e).isSome → ∃ k' < k, ∃ hk' : k' < F.L.lets.length, F.L.lets[k'].e = e) :
    OblSem F.Ξ Γ S := by
  intro e he i ev hev
  obtain ⟨k', hk'k, hk', rfl⟩ := hΓ e he
  exact h k' hk' hk'k i ev hev

/-- **The obligation events are sound**, given that the clauses of `R` hold. -/
theorem obl_sound (σS : Str Voc.toSignature) (h₀ : ∀ j, ∀ ev ∈ σS.D j, ¬ IsLet F.L.lets ev.e)
    (dl : ℕ → ℕ)
    (hsat : ∀ c ∈ F.R, ∀ i, SatRel (applyLets F.L.lets σS) dl (fun _ => True) c i)
    (hobl : ∀ i, ∀ ev ∈ σS.D i, ∀ p, ev.e = F.Ξ.cauN p ∨ ev.e = F.Ξ.supN p →
      ∃ c ∈ F.R, c.ε.name = ev.e) :
    ∀ k ≤ F.L.lets.length, F.OblUpTo (applyLets F.L.lets σS) k := by
  set ℒ := F.L.lets
  set S := applyLets ℒ σS
  have hAL := applyLets_spec' ℒ F.wf.nodup F.scope_names σS h₀ ℒ.length le_rfl
  rw [List.take_length] at hAL
  obtain ⟨-, hbase, hdef⟩ := hAL
  obtain ⟨-, hRcau, hRsup, -⟩ := realization_structure F.hR
  obtain ⟨-, hspec⟩ := typeLets_spec F.lets_body F.wf.nodup F.hT
  intro k
  induction k with
  | zero => intro _ k' _ h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro hk k' hk' hk'k i ev hev
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk'k) with hlt | heq
    · exact ih (by omega) k' hk' hlt i ev hev
    subst heq
    set d := ℒ[k'] with hd
    have hdmem : d ∈ ℒ := List.getElem_mem hk'
    obtain ⟨Tk, -, hTk, -, hCC, hCS⟩ := hspec k' hk'
    have hobl' : OblSem F.Ξ Tk.Γ S := F.oblSem_of_upTo (ih (by omega)) hTk
    have hfvd := F.wf.fv_let d hdmem
    have hcl := (F.wf.clean.2 d hdmem)
    -- an obligation event of `S` is one of `σS`, caused by a clause of `R`
    have hσ : ∀ o ∈ ({F.Ξ.cauN d.e, F.Ξ.supN d.e} : Set Voc.ℰ), ev.e = o → ev ∈ σS.D i := by
      intro o ho he
      rw [← hbase i ev fun k hk _ h => (F.wf.obl_fresh d.e o ho).1 ⟨ℒ[k], List.getElem_mem hk,
        h.symm.trans he⟩]; exact hev
    have hval : ∀ o ∈ ({F.Ξ.cauN d.e, F.Ξ.supN d.e} : Set Voc.ℰ), ev.e = o →
        ∃ v : Val Voc, d.xs.map v = ev.args.map some ∧ v.Covers {y | y ∈ d.xs} ∧
          ∃ ev' : Event Voc.toSignature, ev'.e = d.e ∧ ev'.args = ev.args := by
      intro o ho he
      have hlen : d.xs.length = ev.args.length := by
        rw [F.wf.arity_let d hdmem, ev.arity, he]
        rcases ho with rfl | rfl
        · exact (F.wf.obl_arity d hdmem).1.symm
        · exact (F.wf.obl_arity d hdmem).2.symm
      obtain ⟨v, hv, hdom⟩ := val_of_args d.xs ev.args (F.wf.nodup_xs d hdmem) hlen
      exact ⟨v, hv, fun y hy => (hdom y).2 hy,
        ⟨d.e, ev.args, by rw [← hlen, F.wf.arity_let d hdmem]⟩, rfl, rfl⟩
    refine ⟨fun he => ?_, fun he => ?_⟩
    · -- `Cau_p(ā)` implies `p(ā)`
      obtain ⟨c', hc', hname⟩ := hobl i ev (hσ _ (Set.mem_insert _ _) he) d.e (Or.inl he)
      obtain ⟨f, hf, hfR⟩ := hRcau c' hc' d.e (hname.trans he)
      obtain ⟨body, 𝒞, C₀, hr, hC₀, rfl, hfvb, hclb, -, himp⟩ := hCC f hf
      obtain ⟨v, hv, hvc, ev', he', ha'⟩ := hval _ (Set.mem_insert _ _) he
      have hbody := (rw_sound (dl := dl) hobl' hr C₀ hC₀ {y | y ∈ d.xs} _ (dep_map d.xs ev.args)
        (hclb _ hcl) i v (hvc.mono (Set.union_subset (hfvb.trans hfvd.le) le_rfl)) hv
        fun c hc => satRel_gate (hsat _ (hfR ⟨c, hc, rfl⟩) i) ⟨ev, hev, he, rfl⟩).1 rfl
      refine ⟨ev', (hdef k' hk' hk' i ev' he').2 ⟨v, hvc.mono hfvd.le, by rw [ha']; exact hv,
        himp _ _ _ hbody⟩, he', ha'⟩
    · -- `Sup_p(ā)` implies `¬p(ā)`
      intro ev' hev' he' ha'
      obtain ⟨c', hc', hname⟩ := hobl i ev (hσ _ (Set.mem_insert_of_mem _ rfl) he) d.e (Or.inr he)
      obtain ⟨g, hg, hgR⟩ := hRsup c' hc' d.e (hname.trans he)
      obtain ⟨bs, hbs, rfl, himp⟩ := hCS g hg
      obtain ⟨v, hv, hvc, -⟩ := hval _ (Set.mem_insert_of_mem _ rfl) he
      obtain ⟨v', hv'c, hv'x, hv's⟩ := (hdef k' hk' hk' i ev' he').1 hev'
      refine himp S v i (fun b hb => ?_) ?_
      · obtain ⟨hr, hC, hfvb, hclb, -⟩ := hbs b hb
        exact (rw_sound (dl := dl) hobl' hr b.2.2 hC {y | y ∈ d.xs} _ (dep_map d.xs ev.args)
          (hclb _ hcl) i v (hvc.mono (Set.union_subset (hfvb.trans hfvd.le) le_rfl)) hv
          fun c hc => satRel_gate (hsat _ (hgR ⟨c, ⟨b, hb, hc⟩, rfl⟩) i) ⟨ev, hev, he, rfl⟩).2 rfl
      · refine (Formula.sat_congr _ S v' v i fun y hy => ?_).1 hv's
        have hy' : y ∈ d.xs := by have := hfvd ▸ hy; exact this
        have h1 : d.xs.map v' = d.xs.map v := hv'x.trans (by rw [ha']; exact hv.symm)
        exact (List.map_inj_left.1 h1) y hy'

/-- **The let-normal form holds on the output**, given that the clauses of `R`
    hold there. -/
theorem lnf_sat (σS : Str Voc.toSignature) (h₀ : ∀ j, ∀ ev ∈ σS.D j, ¬ IsLet F.L.lets ev.e)
    (dl : ℕ → ℕ)
    (hsat : ∀ c ∈ F.R, ∀ i, SatRel (applyLets F.L.lets σS) dl (fun _ => True) c i)
    (hobl : ∀ i, ∀ ev ∈ σS.D i, ∀ p, ev.e = F.Ξ.cauN p ∨ ev.e = F.Ξ.supN p →
      ∃ c ∈ F.R, c.ε.name = ev.e) :
    F.L.toFormula.sat σS Val.empty 0 := by
  have hup := F.obl_sound σS h₀ dl hsat hobl F.L.lets.length le_rfl
  obtain ⟨hnl, -⟩ := typeLets_spec F.lets_body F.wf.nodup F.hT
  have hOS : OblSem F.Ξ F.T.Γ (applyLets F.L.lets σS) := by
    refine F.oblSem_of_upTo hup fun e he => ?_
    by_contra hc
    have : ¬ IsLet F.L.lets e := by
      rintro ⟨d, hd, rfl⟩
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
      exact hc ⟨k, hk, hk, rfl⟩
    rw [(hnl e this).1] at he; simp at he
  obtain ⟨hRC, -⟩ := realization_structure F.hR
  have hfv : (bigAnd F.L.chis).fv = ∅ := by
    rw [fv_bigAnd]; ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨χ, hχ, hx⟩; rw [F.wf.closed χ hχ] at hx; exact hx
  have hcl : (bigAnd F.L.chis).Clean ∅ :=
    Clean_bigAnd_of fun χ hχ => ⟨F.wf.clean.1 χ hχ, F.wf.closed χ hχ⟩
  have hmain : ∀ i, (bigAnd F.L.chis).sat (applyLets F.L.lets σS) Val.empty i := by
    intro i
    refine (rw_sound (dl := dl) hOS F.hrw F.C F.hC ∅ (fun _ => True) (fun _ _ _ => Iff.rfl) hcl i
      Val.empty (by rw [hfv]; simp [Val.Covers]) trivial fun c hc => hsat c (hRC hc) i).1 rfl
  have := toFormula_sat F.L.lets F.L.chis σS Val.empty 0
  rw [show (⟨F.L.lets, F.L.chis⟩ : LNF Voc) = F.L from rfl] at this
  rw [this, LNF.body, sat_bigAnd]
  intro φ' hφ'
  obtain ⟨χ, hχ, rfl⟩ := List.mem_map.1 hφ'
  simp only [Formula.Always, Formula.always, Formula.sat, not_exists, not_and, not_not]
  intro j _ _
  exact (sat_bigAnd _ _ _ _).1 (hmain j) χ hχ

end FinalSetting

end Paper
