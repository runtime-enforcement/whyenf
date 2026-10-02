/-
  Theorem 4.3: the output of Algorithm 1 with the enforcer of `P` satisfies `□φ`.
-/
import Paper.Proof.Alg

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem gconj_pastF : ∀ κ : GConj Voc, κ.toFormula.PastF
  | [] => trivial
  | γ :: κ => by
    refine ⟨?_, gconj_pastF κ⟩
    cases γ <;> trivial

theorem gdisj_pastF : ∀ π : GDisj Voc, π.toFormula.PastF
  | [] => trivial
  | κ :: π => ⟨gconj_pastF κ, gdisj_pastF π⟩

namespace Setup
variable (U : Setup Voc)

theorem trig_pastF : ∀ c ∈ U.R, c.trig.PastF := by
  intro c hc
  obtain ⟨rules, -, hrules, -⟩ := U.prog_spec
  obtain ⟨p, -, -, hspec⟩ := forall₂_mem_left hrules c ((U.hrs c).2 hc |> List.mem_mergeSort.2)
  obtain ⟨trig, ht⟩ := hspec.toClause
  obtain ⟨f, hf⟩ := toClause_filter ht
  exact ⟨gdisj_pastF _, (toFilter_basic hf).pastF⟩

/-- The base events of `applyLets ℒ S₀`. -/
theorem applyLets_base {S₀ : Str Voc.toSignature} (h₀ : ∀ j, ∀ ev ∈ S₀.D j, ¬ IsLet U.L.lets ev.e)
    {ev : Event Voc.toSignature} (hev : ¬ IsLet U.L.lets ev.e) (j : ℕ) :
    ev ∈ (applyLets U.L.lets S₀).D j ↔ ev ∈ S₀.D j := by
  have hAL := applyLets_spec' U.L.lets U.wf.nodup U.scope_names S₀ h₀ U.L.lets.length le_rfl
  rw [List.take_length] at hAL
  exact hAL.2.1 j ev fun k hk _ he => hev ⟨_, List.getElem_mem hk, he.symm⟩

variable {U}

section Input
variable (ρ : Trace Voc.toSignature) (hρ : ρ.length = ⊤)
  (hadm : Admissible (NewNames U.Ξ U.L.lets) ρ)

include hρ hadm

theorem hall : ∀ k, ((E U).run ρ k).isSome := fun k => by
  obtain ⟨st, σ, l, h, -⟩ := run_inv ρ hρ hadm k; rw [h]; rfl

theorem limit_exists : ∃ σ : Trace Voc.toSignature,
    σ.seq = .inf ((E U).limitElem ρ (hall ρ hρ hadm)) :=
  ⟨(E U).limit ρ hρ (hall ρ hρ hadm), rfl⟩

/-- The output `ℰ(ρ)`. -/
noncomputable def σo : Trace Voc.toSignature := (limit_exists ρ hρ hadm).choose

theorem σo_seq : (σo ρ hρ hadm).seq = .inf ((E U).limitElem ρ (hall ρ hρ hadm)) :=
  (limit_exists ρ hρ hadm).choose_spec

theorem out_eq : (E U).out ρ = some (σo ρ hρ hadm) := by
  unfold Enforcer.out
  split
  · next l hl => simp [Trace.length, hl, Seq.length] at hρ
  · next f hf => rw [dif_pos (hall ρ hρ hadm), dif_pos (limit_exists ρ hρ hadm)]; rfl

/-- The state after `K` iterations. -/
def At (K : ℕ) (st : EState Voc) (σ : Trace Voc.toSignature) (l : List (ℕ × DB Voc.toSignature)) :
    Prop :=
  (E U).run ρ K = some (some st, σ) ∧ U.RInv st σ l (ρ.τ K)

omit hadm in
theorem exists_at (K : ℕ) (hadm : Admissible (NewNames U.Ξ U.L.lets) ρ) :
    ∃ st σ l, At (U := U) ρ K st σ l ∧ K ≤ l.length := by
  obtain ⟨st, σ, l, h1, h2, h3⟩ := run_inv ρ hρ hadm K
  exact ⟨st, σ, l, ⟨h1, h2⟩, h3⟩

theorem at_later {K K' : ℕ} (hKK' : K ≤ K') {st st' : EState Voc} {σ σ' : Trace Voc.toSignature}
    {l l' : List (ℕ × DB Voc.toSignature)} (h : At (U := U) ρ K st σ l) (h' : At (U := U) ρ K' st' σ' l') :
    st.Ω ⊆ st'.Ω ∧ l <+: l' ∧ ∀ j (hj : j < l'.length), l.length ≤ j → ρ.τ K ≤ l'[j].1 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hKK'
  exact run_later ρ hρ hadm h.1 h.2 d h'.1 h'.2

theorem σo_at {K : ℕ} {st : EState Voc} {σ : Trace Voc.toSignature}
    {l : List (ℕ × DB Voc.toSignature)} (h : At (U := U) ρ K st σ l) {j : ℕ} (hj : j < l.length) :
    (σo ρ hρ hadm).τ j = l[j].1 ∧ (σo ρ hρ hadm).D j = l[j].2 := by
  have := (E U).limitElem_spec ρ (hall ρ hρ hadm) j K (some st, σ) h.1
    (by rw [Enforcer.flen_of_fin h.2.seq]; exact hj)
  simp only [h.2.seq, Seq.get?] at this
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at this
  simp [σo_seq, Trace.τ, Trace.D, Seq.get?, this]

theorem σo_noLet : ∀ j, ∀ ev ∈ (σo ρ hρ hadm).D j, ¬ IsLet U.L.lets ev.e := by
  intro j ev hev
  obtain ⟨st, σ, l, h, hK⟩ := exists_at ρ hρ (j + 1) hadm
  rw [(σo_at ρ hρ hadm h (by omega)).2] at hev
  exact h.2.noLet j (by omega) ev hev

theorem σo_mono {j i : ℕ} (h : j ≤ i) : (σo ρ hρ hadm).τ j ≤ (σo ρ hρ hadm).τ i := by
  induction h with
  | refl => exact le_rfl
  | @step m _ ih =>
    refine le_trans ih ?_
    have := (σo ρ hρ hadm).mono m ((E U).limitElem ρ (hall ρ hρ hadm) m)
      ((E U).limitElem ρ (hall ρ hρ hadm) (m + 1)) (by rw [σo_seq]; rfl) (by rw [σo_seq]; rfl)
    simpa [σo_seq, Trace.τ, Seq.get?] using this

theorem σo_length : (σo ρ hρ hadm).length = ⊤ := by simp [Trace.length, σo_seq, Seq.length]

/-- The time-point at which the obligations of the timestamp `t` are discharged:
    the last time-point with timestamp `t`. -/
noncomputable def dl (t : ℕ) : ℕ :=
  if h : ∃ j, (σo ρ hρ hadm).τ j = t ∧ ∀ j', j < j' → (σo ρ hρ hadm).τ j' ≠ t then
    Classical.choose h else 0

theorem dl_eq {t j : ℕ} (h1 : (σo ρ hρ hadm).τ j = t)
    (h2 : ∀ j', j < j' → (σo ρ hρ hadm).τ j' ≠ t) : dl ρ hρ hadm t = j := by
  have hex : ∃ j, (σo ρ hρ hadm).τ j = t ∧ ∀ j', j < j' → (σo ρ hρ hadm).τ j' ≠ t := ⟨j, h1, h2⟩
  unfold dl; rw [dif_pos hex]
  obtain ⟨c1, c2⟩ := Classical.choose_spec hex
  rcases lt_trichotomy (Classical.choose hex) j with h | h | h
  · exact absurd h1 (c2 j h)
  · exact h
  · exact absurd c1 (h2 _ h)

omit hadm in
theorem progress (t : ℕ) : ∃ K, t < ρ.τ K := by
  obtain ⟨i, p, hp, ht⟩ := ρ.progress hρ t
  exact ⟨i, by simp [Trace.τ, hp, ht]⟩

/-- **Every clause of `R` holds** at every time-point of the output. -/
theorem sat_rel : ∀ c ∈ U.R, ∀ i,
    SatRel (applyLets U.L.lets (σo ρ hρ hadm).toStr) (dl ρ hρ hadm) (fun _ => True) c i := by
  intro c hc i w hw _ htrig
  set σ' := σo ρ hρ hadm with hσ'
  have h₀ : ∀ j, ∀ ev ∈ σ'.toStr.D j, ¬ IsLet U.L.lets ev.e := σo_noLet ρ hρ hadm
  have hbase := fun {ev : Event Voc.toSignature} (h : ¬ IsLet U.L.lets ev.e) j =>
    U.applyLets_base h₀ h j
  have hSτ : (applyLets U.L.lets σ'.toStr).τ = σ'.τ := applyLets_τ _ _
  have hnl : ¬ IsLet U.L.lets c.ε.name := (U.R_props c hc).1.2
  have hlenA : ∀ {a}, Term.evalList w c.ε.args = some a → a.length = Voc.ι c.ε.name :=
    fun ha => (evalList_length ha).trans (U.R_props c hc).1.1
  obtain ⟨a, ha⟩ : ∃ a, Term.evalList w c.ε.args = some a :=
    Option.isSome_iff_exists.1 (U.R_args c hc w fun y hy => hw y (Or.inr hy))
  -- the state after `i + 1` iterations, and the call that produced `i`
  obtain ⟨st, σ, l, hat, hK⟩ := exists_at ρ hρ (i + 1) hadm
  have hi : i < l.length := by omega
  obtain ⟨I, Ω₀, C, S, Ω, hH, hτ, hp, hout, hsub, -⟩ := hat.2.recs i hi
  have hHl : I.H.length = i := by rw [hH]; simp; omega
  have hpt : ∀ k (hk : k ≤ i), σ'.τ k = (l[k]'(by omega)).1 ∧ σ'.D k = (l[k]'(by omega)).2 :=
    fun k hk =>
    σo_at ρ hρ hadm hat (by omega)
  set x : Trip Voc := (Ω, C, S)
  have hagree : PastAgree (applyLets U.L.lets σ'.toStr) (I.St x) i := by
    show PastAgree (applyLets U.L.lets σ'.toStr)
      (applyLets U.L.lets (strOf I.H I.τ (REv.toDB (I.Xof x)))) i
    apply applyLets_past U.L.lets U.pastF
    intro k hk
    rcases Nat.lt_or_eq_of_le hk with hk | rfl
    · have hkH : k < I.H.length := by omega
      rw [strOf_τ_lt _ _ _ hkH, strOf_D_lt _ _ _ hkH]
      have : I.H[k] = l[k] := by simp only [hH, List.getElem_take]
      rw [this]; exact hpt k hk.le
    · have e1 := strOf_τ_len I.H I.τ (REv.toDB (I.Xof x))
      have e2 := strOf_D_len I.H I.τ (REv.toDB (I.Xof x))
      rw [hHl] at e1 e2
      rw [e1, e2, hτ]
      exact ⟨(hpt _ le_rfl).1, (hpt _ le_rfl).2.trans hp⟩
  have htr' : c.trig.sat (I.St x) w I.H.length := by
    rw [hHl]; exact ((U.trig_pastF c hc).sat_congr hagree i le_rfl w).1 htrig
  have hA := I.toPtIn.sat_A hc x hw htr' ha
  have hfix := hout.fix c hc
  have hli : (l.take i).length = i := by simp; omega
  rw [hli] at hfix
  -- the time-point `i` of the output
  have hDi : σ'.D i = REv.toDB ((I.D \ S) ∪ C) := (hpt i le_rfl).2.trans hp
  have hτi : σ'.τ i = I.τ := (hpt i le_rfl).1.trans hτ.symm
  have hpred : ∀ j e (ts : List (Term Voc)), Term.evalList w ts = some a → ¬ IsLet U.L.lets e →
      ∀ (ev : Event Voc.toSignature), ev ∈ σ'.D j → ev.e = e → ev.args = a →
        (Formula.pred e ts).sat (applyLets U.L.lets σ'.toStr) w j := by
    intro j e ts hts he ev hev h1 h2
    exact ⟨a, hts, ev, (hbase (h1 ▸ he) j).2 hev, h1, h2⟩
  cases hε : c.ε with
  | cau e ts =>
    have hm : (e, a) ∈ C := hfix.2.1 (show (e, a) ∈ (I.toPtIn.Δ i c x).2.1 by
      simp only [PtIn.Δ, hε]; exact ⟨rfl, hA⟩)
    rw [hε] at ha hnl hlenA
    simp only [Effect.Holds]
    refine hpred i e ts ha hnl ⟨e, a, hlenA ha⟩ ?_ rfl rfl
    rw [hDi]; exact Or.inr hm
  | sup e ts =>
    have hm : (e, a) ∈ S := hfix.2.2 (show (e, a) ∈ (I.toPtIn.Δ i c x).2.2 by
      simp only [PtIn.Δ, hε]; exact ⟨rfl, hA⟩)
    rw [hε] at ha hnl
    simp only [Effect.Holds]
    rintro ⟨ds, hds, ev, hev, h1, h2⟩
    have ha' : Term.evalList w ts = some a := ha
    rw [ha'] at hds; cases hds
    rw [hbase (h1 ▸ hnl) i] at hev
    change ev ∈ σ'.D i at hev
    rw [hDi] at hev
    have : (ev.e, ev.args) = (e, a) := by rw [h1, h2]
    rcases hev with ⟨-, h⟩ | h
    · exact h (this ▸ hm)
    · exact hout.disj _ hm (this ▸ h)
  | ev J e ts =>
    obtain ⟨⟨n, hn1, hJ⟩, -⟩ : Effect.OK U.Ξ (.ev J e ts) := hε ▸ U.R_ok c hc
    set o : Obligation Voc := ((e, a), (.ts, I.τ + n))
    have ho : o ∈ Ω := hfix.1 (show o ∈ (I.toPtIn.Δ i c x).1 by
      simp only [PtIn.Δ, hε]; exact ⟨n, hJ, rfl, hA, rfl⟩)
    rw [hε] at ha hnl
    simp only [Effect.Holds]
    intro n' hn'
    rw [hJ] at hn'; have := icc_inj hn'; subst this
    rw [hSτ, hτi]
    set t := I.τ + n
    obtain ⟨K₁, hK₁⟩ := progress ρ hρ t
    obtain ⟨st₂, σ₂, l₂, hat₂, hK₂⟩ := exists_at ρ hρ (max K₁ (i + 1)) hadm
    have hΩ₂ := (at_later ρ hρ hadm (le_max_right _ _) hat hat₂).1
    have ht₂ : t < ρ.τ (max K₁ (i + 1)) := lt_of_lt_of_le hK₁ (τ_mono' ρ hρ (le_max_left _ _))
    obtain ⟨j, hj, h1, h2, h3⟩ := hat₂.2.ts o (hΩ₂ (hsub ho)) t rfl ht₂
    have hσj := σo_at ρ hρ hadm hat₂ hj
    have hdl : dl ρ hρ hadm t = j := by
      refine dl_eq ρ hρ hadm (hσj.1.trans h1) fun j' hjj' => ?_
      by_cases hj' : j' < l₂.length
      · rw [(σo_at ρ hρ hadm hat₂ hj').1]; exact (h3 j' hj' hjj').ne'
      · obtain ⟨st₃, σ₃, l₃, hat₃, hK₃⟩ :=
          exists_at ρ hρ (max (j' + 1) (max K₁ (i + 1))) hadm
        have hb := (at_later ρ hρ hadm (le_max_right _ _) hat₂ hat₃).2.2 j' (by omega) (by omega)
        rw [(σo_at ρ hρ hadm hat₃ (by omega)).1]
        omega
    rw [hdl]
    refine ⟨?_, hσj.1.trans h1, ?_⟩
    · by_contra hlt
      have := σo_mono ρ hρ hadm (le_of_lt (not_le.1 hlt))
      rw [hσj.1, h1, hτi] at this; omega
    · obtain ⟨ev, hev, hraw⟩ := h2
      have hraw' : (ev.e, ev.args) = (e, a) := hraw
      obtain ⟨r1, r2⟩ := Prod.mk.inj hraw'
      exact hpred j e ts ha hnl ev (hσj.2 ▸ hev) r1 r2
  | nexts n e ts =>
    obtain ⟨hn1, -⟩ : Effect.OK U.Ξ (.nexts n e ts) := hε ▸ U.R_ok c hc
    set o : Obligation Voc := ((e, a), (.tp, i + n))
    have ho : o ∈ Ω := hfix.1 (show o ∈ (I.toPtIn.Δ i c x).1 by
      simp only [PtIn.Δ, hε]; exact ⟨rfl, hA, rfl⟩)
    rw [hε] at ha hnl
    simp only [Effect.Holds]
    obtain ⟨st₂, σ₂, l₂, hat₂, hK₂⟩ := exists_at ρ hρ (i + n + 1) hadm
    have hΩ₂ := (at_later ρ hρ hadm (by omega) hat hat₂).1
    have hin : i + n < l₂.length := by omega
    refine ⟨?_, fun h1 => ?_⟩
    · obtain ⟨ev, hev, hraw⟩ := hat₂.2.tp o (hΩ₂ (hsub ho)) (i + n) hin rfl
      have hraw' : (ev.e, ev.args) = (e, a) := hraw
      obtain ⟨r1, r2⟩ := Prod.mk.inj hraw'
      exact hpred (i + n) e ts ha hnl ev ((σo_at ρ hρ hadm hat₂ hin).2 ▸ hev) r1 r2
    · subst h1
      have hg := hat₂.2.gap o (hΩ₂ (hsub ho)) i hin rfl
      rw [hSτ, (σo_at ρ hρ hadm hat₂ hin).1, (σo_at ρ hρ hadm hat₂ (by omega)).1]
      exact hg

/-- The obligation events of the output come from clauses of `R`. -/
theorem obl_out : ∀ i, ∀ ev ∈ (σo ρ hρ hadm).toStr.D i, ∀ p,
    ev.e = U.Ξ.cauN p ∨ ev.e = U.Ξ.supN p → ∃ c ∈ U.R, c.ε.name = ev.e := by
  intro i ev hev p hp
  obtain ⟨st, σ, l, hat, hK⟩ := exists_at ρ hρ (i + 1) hadm
  obtain ⟨I, Ω₀, C, S, Ω, hH, hτ, hpd, hout, hsub, hDn⟩ := hat.2.recs i (by omega)
  change ev ∈ (σo ρ hρ hadm).D i at hev
  rw [(σo_at ρ hρ hadm hat (by omega)).2, hpd] at hev
  rcases hev with ⟨h, -⟩ | h
  · exact absurd (by rcases hp with hp | hp; exact Or.inl ⟨p, hp.symm⟩; exact Or.inr ⟨p, hp.symm⟩)
      (hDn _ h)
  · exact hout.nameC _ h

/-- **The output satisfies `□φ`.** -/
theorem out_sat : (Formula.Always U.φ).satTr (σo ρ hρ hadm) Val.empty 0 := by
  have h₀ : ∀ j, ∀ ev ∈ (σo ρ hρ hadm).toStr.D j, ¬ IsLet U.L.lets ev.e := σo_noLet ρ hρ hadm
  have hL := U.lnf_sat (σo ρ hρ hadm).toStr h₀ (dl ρ hρ hadm) (sat_rel ρ hρ hadm) (obl_out ρ hρ hadm)
  exact (U.equiv _ (σo_length ρ hρ hadm) fun i ev hev => σo_noLet ρ hρ hadm i ev hev).2 ⟨σo_length ρ hρ hadm, hL⟩

end Input

/-- **`P` is a sound enforcer for `□φ`.** -/
theorem sound (U : Setup Voc) : U.P.SoundEnforcer U.Ξ.CauAll U.Ξ.Sup
    (Admissible (NewNames U.Ξ U.L.lets)) (Formula.Always U.φ) := by
  intro _ ρ hρ hadm
  refine ⟨fun k st h => ?_, σo ρ hρ hadm, out_eq ρ hρ hadm, out_sat ρ hρ hadm⟩
  obtain ⟨st', σ, l, h', -⟩ := run_inv ρ hρ hadm k
  rw [h] at h'
  cases h'; rfl

end Setup

/-- **Theorem 4.3** (Compilation correctness). -/
theorem theorem_4_3 : Theorem_4_3 Voc := by
  intro Ξ LNF φ hmf hcl L hvalid hwf hequiv T hT R hRw hconf hO rk htopo rs hrs evTys colTy P hP
  obtain ⟨𝒞, hrw, C, hC, hR⟩ := hRw
  obtain ⟨O, hdfg⟩ := hO
  exact Setup.sound
    { Ξ := Ξ, φ := φ, L := L, valid := hvalid, wf := hwf, T := T, hT := hT, 𝒞 := 𝒞, hrw := hrw,
      C := C, hC := hC, R := R, hR := hR, mfotl := hmf, closed := hcl, equiv := hequiv,
      conflict := hconf, O := O, dfg := hdfg, rk := rk, topo := htopo, rs := rs, hrs := hrs,
      evTys := evTys, colTy := colTy, P := P, hP := hP }

end Paper
