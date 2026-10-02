/-
  Algorithm 1 with the enforcer of `P`: the invariant of the run.
-/
import Paper.Proof.Run

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem getElem_snoc {α : Type} {l : List α} {p : α} {m : ℕ} (hm : m < (l ++ [p]).length) :
    (l ++ [p])[m] = if h : m < l.length then l[m] else p := by
  split_ifs with h
  · exact List.getElem_append_left h
  · have : m = l.length := by simp at hm; omega
    subst this; simp

theorem take_snoc {α : Type} {l : List α} {p : α} {j : ℕ} (hj : j ≤ l.length) :
    (l ++ [p]).take j = l.take j := List.take_append_of_le_length hj

/-- Appending to a finite trace. -/
theorem snoc?_fin {Sig : Signature} {σ : Trace Sig} {l : List (ℕ × DB Sig)} (hs : σ.seq = .fin l)
    {τ : ℕ} {D : DB Sig} (hD : D.Finite) (hτ : ∀ m (hm : m < l.length), l[m].1 ≤ τ) :
    ∃ σ', σ.snoc? τ D = some σ' ∧ σ'.seq = .fin (l ++ [(τ, D)]) := by
  have hc : σ.CanSnoc τ D := by
    refine ⟨⟨l, hs⟩, hD, fun τ' h => ?_⟩
    rw [Trace.lastTs?_of_fin hs] at h
    simp only [Option.mem_def, Option.map_eq_some_iff] at h
    obtain ⟨p, hp, rfl⟩ := h
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem (List.mem_of_getLast? hp)
    exact hτ m hm
  refine ⟨σ.snoc τ D hc, by simp [Trace.snoc?, hc], ?_⟩
  have hs' : Seq.fin (Classical.choose hc.1) = Seq.fin l := (Classical.choose_spec hc.1).symm.trans hs
  injection hs' with h
  simp only [Trace.snoc, h]

theorem len_fin {Sig : Signature} {σ : Trace Sig} {l : List (ℕ × DB Sig)} (hs : σ.seq = .fin l) :
    Trace.len σ = l.length := by
  simp [Trace.len, Trace.length, hs, Seq.length]

theorem raw_mem {D : DB Voc.toSignature} {ev : Event Voc.toSignature} :
    (ev.e, ev.args) ∈ Event.raw '' D ↔ ev ∈ D := by
  constructor
  · rintro ⟨ev', h, he⟩
    have : ev' = ev := by
      simp only [Event.raw, Prod.mk.injEq] at he; exact Event.ext he.1 he.2
    exact this ▸ h
  · intro h; exact ⟨ev, h, rfl⟩

theorem toDB_raw (D : DB Voc.toSignature) (S C : Set (REv Voc)) :
    REv.toDB ((Event.raw '' D \ S) ∪ C) = (D \ REv.toDB S) ∪ REv.toDB C := by
  ext ev
  simp only [REv.toDB, Set.mem_setOf_eq, Set.mem_union, Set.mem_sdiff, raw_mem]

theorem toDB_empty (S C : Set (REv Voc)) : REv.toDB ((∅ \ S) ∪ C) = REv.toDB C := by
  simp

theorem toDB_finite {C : Set (REv Voc)} (h : C.Finite) : (REv.toDB C).Finite :=
  h.preimage (f := Event.raw) fun a _ b _ hab => by
    simp only [Event.raw, Prod.mk.injEq] at hab; exact Event.ext hab.1 hab.2

theorem mem_raw_toDB {C : Set (REv Voc)} {x : REv Voc} (hx : x ∈ C)
    (hl : x.2.length = Voc.ι x.1) : x ∈ Event.raw '' REv.toDB C :=
  ⟨⟨x.1, x.2, hl⟩, hx, rfl⟩

namespace Setup
variable (U : Setup Voc)

open TIn

/-- The record of the call of `Saturate` that produced the time-point `p`
    after the history `H`; its obligations are among `Ωc`. -/
def PtRec (H : List (ℕ × DB Voc.toSignature)) (p : ℕ × DB Voc.toSignature)
    (Ωc : Set (Obligation Voc)) : Prop :=
  ∃ (I : U.TIn) (Ω₀ : Set (Obligation Voc)) (C S : Set (REv Voc)) (Ω : Set (Obligation Voc)),
    I.H = H ∧ I.τ = p.1 ∧ p.2 = REv.toDB ((I.D \ S) ∪ C) ∧ I.CallOut Ω₀ H.length C S Ω ∧ Ω ⊆ Ωc ∧
      ∀ x ∈ I.D, x.1 ∉ Set.range U.Ξ.cauN ∪ Set.range U.Ξ.supN

/-- **The invariant of Algorithm 1**, with the output `σ = l` so far, the state
    `st`, and the next time `now` at which `μ` or `ν` is called. -/
structure RInv (st : EState Voc) (σ : Trace Voc.toSignature) (l : List (ℕ × DB Voc.toSignature))
    (now : ℕ) : Prop where
  seq : σ.seq = .fin l
  tab : st.T = TablesOf U.L.lets l
  noLet : ∀ m (hm : m < l.length), ∀ ev ∈ l[m].2, ¬ IsLet U.L.lets ev.e
  le_now : ∀ m (hm : m < l.length), l[m].1 ≤ now
  tf : (TVals U l).Finite
  Ωf : st.Ω.Finite
  ok : ∀ o ∈ st.Ω, ObOK U o
  tp : ∀ o ∈ st.Ω, ∀ j (hj : j < l.length), o.2 = (.tp, j) → o.1 ∈ Event.raw '' l[j].2
  ts : ∀ o ∈ st.Ω, ∀ t, o.2 = (.ts, t) → t < now → ∃ j, ∃ hj : j < l.length, l[j].1 = t ∧
    o.1 ∈ Event.raw '' l[j].2 ∧ ∀ j' (hj' : j' < l.length), j < j' → t < l[j'].1
  gapNow : ∀ o ∈ st.Ω, o.2 = (.tp, l.length) →
    ∃ h : 0 < l.length, now ≤ (l[l.length - 1]'(by omega)).1 + 1
  gap : ∀ o ∈ st.Ω, ∀ j (hj : j + 1 < l.length), o.2 = (.tp, j + 1) →
    l[j + 1].1 ≤ (l[j]'(by omega)).1 + 1
  recs : ∀ j (hj : j < l.length), U.PtRec (l.take j) l[j] st.Ω

theorem RInv.init (now : ℕ) : U.RInv EState.init Trace.empty [] now := by
  refine ⟨rfl, (TablesOf_nil _).symm, fun m hm => absurd hm (Nat.not_lt_zero _),
    fun m hm => absurd hm (Nat.not_lt_zero _), ?_, Set.finite_empty, ?_, ?_, ?_, ?_, ?_,
    fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · refine Set.finite_empty.subset ?_
    rintro x ⟨q, tr, h, -⟩; rw [TablesOf_nil] at h; exact h
  all_goals intro o ho; exact absurd ho (Set.notMem_empty _)

variable {U}

/-- **A call that produces a time-point** at `now`; the next call is at `now'`. -/
theorem RInv.point {st : EState Voc} {σ : Trace Voc.toSignature} {l : List (ℕ × DB Voc.toSignature)}
    {now : ℕ} (hI : U.RInv st σ l now) (I : U.TIn) (hH : I.H = l) (hτ : I.τ = now)
    (hDn : ∀ x ∈ I.D, x.1 ∉ Set.range U.Ξ.cauN ∪ Set.range U.Ξ.supN)
    (hC₀ : ∀ e, (e, (DKind.tp, l.length)) ∈ st.Ω → e ∈ I.C₀)
    {C S : Set (REv Voc)} {Ω : Set (Obligation Voc)} (hout : I.CallOut st.Ω l.length C S Ω)
    (now' : ℕ) (hnow : now ≤ now') (hnow' : now' ≤ now + 1)
    (hts : now' = now + 1 → ∀ e, (e, (DKind.ts, now)) ∈ st.Ω → e ∈ I.C₀)
    {σ' : Trace Voc.toSignature} (hσ' : σ'.seq = .fin (l ++ [(now, REv.toDB ((I.D \ S) ∪ C))])) :
    U.RInv ⟨TablesOf U.L.lets (l ++ [(now, REv.toDB ((I.D \ S) ∪ C))]), st.TN, Ω⟩ σ'
      (l ++ [(now, REv.toDB ((I.D \ S) ∪ C))]) now' := by
  set p : ℕ × DB Voc.toSignature := (now, REv.toDB ((I.D \ S) ∪ C)) with hp
  have hlen : (l ++ [p]).length = l.length + 1 := by simp
  -- the new obligations
  have hnew : ∀ o ∈ Ω, o ∉ st.Ω → ObOK U o ∧
      ((∃ n, 1 ≤ n ∧ o.2 = (.ts, now + n)) ∨ (∃ n, 1 ≤ n ∧ o.2 = (.tp, l.length + n))) := by
    intro o ho hno
    obtain ⟨h1, h2⟩ := hout.newΩ o ho hno
    rw [hτ] at h2; exact ⟨h1, h2⟩
  have hC : ∀ e ∈ C, e ∈ Event.raw '' p.2 := fun e he =>
    mem_raw_toDB (Or.inr he) (hout.goodC e he).1
  refine ⟨hσ', rfl, ?_, ?_, ?_, hout.finΩ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- no let events
    intro m hm ev hev
    rw [getElem_snoc] at hev
    split_ifs at hev with h
    · exact hI.noLet m h ev hev
    · rcases hev with ⟨h1, -⟩ | h1
      · exact (I.hD _ h1).2
      · exact (hout.goodC _ h1).2
  · intro m hm
    rw [getElem_snoc]; split_ifs with h
    · exact le_trans (hI.le_now m h) hnow
    · exact hnow
  · have := hout.tabs; rw [hH, hτ] at this; exact this
  · intro o ho
    by_cases h : o ∈ st.Ω
    · exact hI.ok o h
    · exact (hnew o ho h).1
  · -- time-point obligations
    intro o ho j hj hk
    rw [getElem_snoc]
    split_ifs with h
    · by_cases h' : o ∈ st.Ω
      · exact hI.tp o h' j h hk
      · rcases (hnew o ho h').2 with ⟨n, -, hn⟩ | ⟨n, hn1, hn⟩ <;> rw [hn] at hk <;>
          simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hk
        omega
    · have hj' : j = l.length := by rw [hlen] at hj; omega
      subst hj'
      by_cases h' : o ∈ st.Ω
      · exact hC _ (hout.C₀_sub (hC₀ o.1 (by rw [← hk]; exact h')))
      · rcases (hnew o ho h').2 with ⟨n, -, hn⟩ | ⟨n, hn1, hn⟩ <;> rw [hn] at hk <;>
          simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hk
        omega
  · -- timestamp obligations
    intro o ho t hk ht
    by_cases h' : o ∈ st.Ω
    · by_cases htn : t < now
      · obtain ⟨j, hj, h1, h2, h3⟩ := hI.ts o h' t hk htn
        refine ⟨j, by rw [hlen]; omega, ?_, ?_, fun j' hj' hjj' => ?_⟩
        · rw [getElem_snoc, dif_pos hj]; exact h1
        · rw [getElem_snoc, dif_pos hj]; exact h2
        · rw [getElem_snoc]; split_ifs with h
          · exact h3 j' h hjj'
          · exact htn
      · have htn' : t = now := by omega
        subst htn'
        have hnow1 : now' = t + 1 := by omega
        refine ⟨l.length, by rw [hlen]; omega, ?_, ?_, fun j' hj' hjj' => ?_⟩
        · rw [getElem_snoc, dif_neg (lt_irrefl _)]
        · rw [getElem_snoc, dif_neg (lt_irrefl _)]
          exact hC _ (hout.C₀_sub (hts hnow1 o.1 (by rw [← hk]; exact h')))
        · rw [hlen] at hj'; omega
    · rcases (hnew o ho h').2 with ⟨n, hn1, hn⟩ | ⟨n, -, hn⟩ <;> rw [hn] at hk <;>
        simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hk
      omega
  · -- the gap before the next time-point
    intro o ho hk
    refine ⟨by rw [hlen]; omega, ?_⟩
    have : (l ++ [p])[(l ++ [p]).length - 1]'(by rw [hlen]; omega) = p := by
      rw [getElem_snoc, dif_neg (by rw [hlen]; omega)]
    rw [this]; omega
  · intro o ho j hj hk
    rw [getElem_snoc, getElem_snoc]
    by_cases h' : o ∈ st.Ω
    · split_ifs with h1 h2 h2
      · exact hI.gap o h' j h1 hk
      · omega
      · have hj' : j = l.length - 1 := by omega
        subst hj'
        have hl : l.length - 1 + 1 = l.length := by omega
        obtain ⟨h0, hle⟩ := hI.gapNow o h' (by rw [hk, hl])
        exact hle
      · omega
    · rcases (hnew o ho h').2 with ⟨n, -, hn⟩ | ⟨n, hn1, hn⟩ <;> rw [hn] at hk <;>
        simp only [Prod.mk.injEq, reduceCtorEq, false_and] at hk
      have : l.length + 1 ≤ j + 1 := by omega
      rw [hlen] at hj; omega
  · -- the records
    intro j hj
    rw [getElem_snoc]
    split_ifs with h
    · rw [take_snoc h.le]
      obtain ⟨I', Ω₀', C', S', Ω', h1, h2, h3, h4, h5, h6⟩ := hI.recs j h
      exact ⟨I', Ω₀', C', S', Ω', h1, h2, h3, h4, h5.trans hout.Ω_sub, h6⟩
    · have hj' : j = l.length := by rw [hlen] at hj; omega
      subst hj'
      rw [take_snoc le_rfl, List.take_length]
      exact ⟨I, st.Ω, C, S, Ω, hH, hτ, rfl, hH ▸ hout, le_rfl, hDn⟩

/-- **The call of `μ`** at `τ` with the input `Din`. -/
theorem RInv.muStep {st : EState Voc} {σ : Trace Voc.toSignature} {l : List (ℕ × DB Voc.toSignature)}
    {τ : ℕ} (hI : U.RInv st σ l τ) {Din : DB Voc.toSignature} (hDf : Din.Finite)
    (hDl : ∀ ev ∈ Din, ¬ IsLet U.L.lets ev.e)
    (hDn : ∀ ev ∈ Din, ev.e ∉ Set.range U.Ξ.cauN ∪ Set.range U.Ξ.supN) :
    ∃ st' C' S', (U.P.enforcer U.Ξ.CauAll U.Ξ.Sup).μ (some st) σ τ Din = (some st', C', S') ∧
      ∃ σ', σ.snoc? τ ((Din \ S'.1) ∪ C'.1) = some σ' ∧
        U.RInv st' σ' (l ++ [(τ, (Din \ S'.1) ∪ C'.1)]) τ ∧ st.Ω ⊆ st'.Ω := by
  have hlen := len_fin hI.seq
  set O : Set (REv Voc) := {e | (e, (DKind.tp, Trace.len σ)) ∈ st.Ω} with hO
  have hOk : ∀ e ∈ O, ObOK U (e, (DKind.tp, Trace.len σ)) := fun e he => hI.ok _ he
  have hOg : U.Good O := fun e he => (hOk e he).1
  have hOf : O.Finite := (hI.Ωf.image Prod.fst).subset fun e he => ⟨_, he, rfl⟩
  have hDg : U.Good (Event.raw '' Din) := by
    rintro _ ⟨ev, hev, rfl⟩; exact ⟨ev.arity, hDl ev hev⟩
  let I : U.TIn := ⟨⟨l, τ, Event.raw '' Din, hI.noLet, hI.le_now, hDg⟩, O, hOg, hDf.image _, hOf,
    hI.tf⟩
  obtain ⟨C, S, Ω, hsat, hout⟩ := I.call_spec hI.Ωf (fun e he => (hOk e he).2) st.TN σ
  rw [hlen] at hout
  have hdb : REv.InDB C U.Ξ.CauAll ∧ REv.InDB S U.Ξ.Sup :=
    ⟨fun x hx => ⟨hout.inC x hx, (hout.goodC x hx).1⟩, fun x hx => ⟨hout.inS x hx, (hout.goodS x hx).1⟩⟩
  have hsat' : Saturate U.P ⟨st.T, τ, Event.raw '' Din, O, ∅⟩ st.TN st.Ω σ =
      some (TablesOf U.L.lets (l ++ [(τ, REv.toDB ((Event.raw '' Din \ S) ∪ C))]), C, S, Ω) := by
    rw [hI.tab]; exact hsat
  have hmu : mu U.P st σ τ (Event.raw '' Din) = some
      (⟨TablesOf U.L.lets (l ++ [(τ, REv.toDB ((Event.raw '' Din \ S) ∪ C))]), st.TN, Ω⟩, C, S) := by
    unfold mu; simp only []; rw [hsat']; rfl
  refine ⟨⟨TablesOf U.L.lets (l ++ [(τ, REv.toDB ((Event.raw '' Din \ S) ∪ C))]), st.TN, Ω⟩,
    ⟨REv.toDB C, REv.toDB_mem hdb.1⟩, ⟨REv.toDB S, REv.toDB_mem hdb.2⟩, ?_, ?_⟩
  · simp only [Program.enforcer, hmu, dif_pos hdb]
  · dsimp only
    rw [← toDB_raw]
    obtain ⟨σ', h1, h2⟩ := snoc?_fin hI.seq (τ := τ)
      (toDB_finite (((hDf.image _).sdiff).union hout.finC)) hI.le_now
    refine ⟨σ', h1, hI.point I rfl rfl (by rintro _ ⟨ev, hev, rfl⟩; exact hDn ev hev) (fun e he => by show _ ∈ st.Ω; rw [hlen]; exact he) hout τ
      le_rfl (by omega) (fun h => by omega) h2, hout.Ω_sub⟩

/-- **The call of `ν`** at `t`. -/
theorem RInv.nuStep {st : EState Voc} {σ : Trace Voc.toSignature} {l : List (ℕ × DB Voc.toSignature)}
    {t : ℕ} (hI : U.RInv st σ l t) :
    (∃ st', (U.P.enforcer U.Ξ.CauAll U.Ξ.Sup).ν (some st) σ t = (some st', none) ∧
        U.RInv st' σ l (t + 1) ∧ st.Ω ⊆ st'.Ω) ∨
      (∃ st' C', (U.P.enforcer U.Ξ.CauAll U.Ξ.Sup).ν (some st) σ t = (some st', some C') ∧
        ∃ σ', σ.snoc? t C'.1 = some σ' ∧ U.RInv st' σ' (l ++ [(t, C'.1)]) (t + 1) ∧
          st.Ω ⊆ st'.Ω) := by
  have hlen := len_fin hI.seq
  set O : Set (REv Voc) :=
    {e | (e, (DKind.tp, Trace.len σ)) ∈ st.Ω ∨ (e, (DKind.ts, t)) ∈ st.Ω} with hO
  by_cases hC : O = ∅
  · left
    have hnu : nu U.P st σ t = some (st, none) := by
      unfold nu; simp only []; rw [if_pos hC]
    refine ⟨st, by simp only [Program.enforcer, hnu], ?_, le_rfl⟩
    have hno : ∀ e, (e, (DKind.tp, l.length)) ∉ st.Ω ∧ (e, (DKind.ts, t)) ∉ st.Ω := by
      intro e
      have : e ∉ O := by rw [hC]; exact Set.notMem_empty _
      simp only [hO, Set.mem_setOf_eq, not_or, hlen] at this
      exact this
    refine ⟨hI.seq, hI.tab, hI.noLet, fun m hm => le_trans (hI.le_now m hm) (by omega), hI.tf, hI.Ωf,
      hI.ok, hI.tp, ?_, ?_, hI.gap, hI.recs⟩
    · intro o ho t' hk ht'
      by_cases h : t' < t
      · exact hI.ts o ho t' hk h
      · have : t' = t := by omega
        subst this
        exact absurd (show (o.1, (DKind.ts, t')) ∈ st.Ω by rw [← hk]; exact ho) (hno o.1).2
    · intro o ho hk
      exact absurd (show (o.1, (DKind.tp, l.length)) ∈ st.Ω by rw [← hk]; exact ho) (hno o.1).1
  · right
    have hOk : ∀ e ∈ O, ∃ k, ObOK U (e, k) := by
      rintro e (he | he)
      · exact ⟨_, hI.ok _ he⟩
      · exact ⟨_, hI.ok _ he⟩
    have hOg : U.Good O := fun e he => (hOk e he).choose_spec.1
    have hOf : O.Finite := (hI.Ωf.image Prod.fst).subset fun e he => by
      rcases he with he | he
      · exact ⟨_, he, rfl⟩
      · exact ⟨_, he, rfl⟩
    have hDg : U.Good (∅ : Set (REv Voc)) := fun e he => absurd he (Set.notMem_empty _)
    let I : U.TIn := ⟨⟨l, t, ∅, hI.noLet, hI.le_now, hDg⟩, O, hOg, Set.finite_empty, hOf, hI.tf⟩
    obtain ⟨C, S, Ω, hsat, hout⟩ := I.call_spec hI.Ωf (fun e he => (hOk e he).choose_spec.2) st.TN σ
    rw [hlen] at hout
    have hdb : REv.InDB C U.Ξ.CauAll := fun x hx => ⟨hout.inC x hx, (hout.goodC x hx).1⟩
    have hsat' : Saturate U.P ⟨st.T, t, ∅, O, ∅⟩ st.TN st.Ω σ =
        some (TablesOf U.L.lets (l ++ [(t, REv.toDB ((∅ \ S) ∪ C))]), C, S, Ω) := by
      rw [hI.tab]; exact hsat
    have hnu : nu U.P st σ t = some
        (⟨TablesOf U.L.lets (l ++ [(t, REv.toDB ((∅ \ S) ∪ C))]), st.TN, Ω⟩, some C) := by
      unfold nu; simp only []; rw [if_neg hC, hsat']; rfl
    refine ⟨⟨TablesOf U.L.lets (l ++ [(t, REv.toDB ((∅ \ S) ∪ C))]), st.TN, Ω⟩,
      ⟨REv.toDB C, REv.toDB_mem hdb⟩, ?_, ?_⟩
    · simp only [Program.enforcer, hnu, dif_pos hdb]
    · dsimp only
      obtain ⟨σ', h1, h2⟩ := snoc?_fin hI.seq (τ := t) (toDB_finite hout.finC)
        (fun m hm => hI.le_now m hm)
      have h2' : σ'.seq = .fin (l ++ [(t, REv.toDB ((I.D \ S) ∪ C))]) := by
        rw [h2]; show _ = Seq.fin (l ++ [(t, REv.toDB ((∅ \ S) ∪ C))]); rw [toDB_empty]
      have hR := hI.point I rfl rfl (fun x hx => absurd hx (Set.notMem_empty _)) (fun e he => Or.inl (by rw [hlen]; exact he)) hout (t + 1)
        (by omega) le_rfl (fun _ e he => Or.inr he) h2'
      refine ⟨σ', h1, ?_, hout.Ω_sub⟩
      have e1 : REv.toDB ((I.D \ S) ∪ C) = REv.toDB C := toDB_empty S C
      rw [e1] at hR
      convert hR using 2
      rw [show (∅ : Set (REv Voc)) \ S ∪ C = C by simp]

/-- The enforcer of `P`. -/
noncomputable abbrev E (U : Setup Voc) : Enforcer Voc.toSignature U.Ξ.CauAll U.Ξ.Sup :=
  U.P.enforcer U.Ξ.CauAll U.Ξ.Sup

/-- **The loop of line 4** over `t, …, t + m - 1`. -/
theorem RInv.proLoop : ∀ (m t : ℕ) {st : EState Voc} {σ : Trace Voc.toSignature}
    {l : List (ℕ × DB Voc.toSignature)}, U.RInv st σ l t →
    ∃ st' σ' l', (E U).proLoop (List.range' t m) (some st, σ) = some (some st', σ') ∧
      U.RInv st' σ' l' (t + m) ∧ st.Ω ⊆ st'.Ω ∧ l <+: l' ∧
      ∀ j (hj : j < l'.length), l.length ≤ j → t ≤ l'[j].1
  | 0, t, st, σ, l, hI => ⟨st, σ, l, rfl, hI, le_rfl, List.prefix_refl _, fun j hj h => by omega⟩
  | m + 1, t, st, σ, l, hI => by
    rw [List.range'_succ]
    rcases hI.nuStep with ⟨st1, hν, hI1, hΩ1⟩ | ⟨st1, C', hν, σ1, hs, hI1, hΩ1⟩
    · obtain ⟨st', σ', l', h1, h2, h3, h4, h5⟩ := RInv.proLoop m (t + 1) hI1
      refine ⟨st', σ', l', ?_, by rw [show t + (m + 1) = t + 1 + m by omega]; exact h2,
        hΩ1.trans h3, h4, fun j hj h => le_trans (Nat.le_succ t) (h5 j hj h)⟩
      simp only [Enforcer.proLoop, hν]; exact h1
    · obtain ⟨st', σ', l', h1, h2, h3, h4, h5⟩ := RInv.proLoop m (t + 1) hI1
      refine ⟨st', σ', l', ?_, by rw [show t + (m + 1) = t + 1 + m by omega]; exact h2,
        hΩ1.trans h3, (List.prefix_append l _).trans h4, fun j hj h => ?_⟩
      · simp only [Enforcer.proLoop, hν, hs, Option.bind_some]; exact h1
      · by_cases hj' : j = l.length
        · subst hj'
          obtain ⟨u, hu⟩ := h4
          have : l'[l.length] = (l ++ [(t, C'.1)])[l.length]'(by simp) := by
            simp only [← hu]; rw [List.getElem_append_left]
          rw [this]; simp
        · exact le_trans (Nat.le_succ t) (h5 j hj (by simp; omega))

section Input
variable (ρ : Trace Voc.toSignature) (hρ : ρ.length = ⊤)
  (hadm : Admissible (NewNames U.Ξ U.L.lets) ρ)
include hρ

theorem inf_of_top : ∃ f, ρ.seq = .inf f := by
  cases h : ρ.seq with
  | fin l => simp [Trace.length, h, Seq.length] at hρ
  | inf f => exact ⟨f, rfl⟩

theorem τ_mono (k : ℕ) : ρ.τ k ≤ ρ.τ (k + 1) := by
  obtain ⟨f, hf⟩ := inf_of_top ρ hρ
  have := ρ.mono k (f k) (f (k + 1)) (by simp [hf, Seq.get?]) (by simp [hf, Seq.get?])
  simpa [Trace.τ, hf, Seq.get?] using this

theorem τ_mono' {k k' : ℕ} (h : k ≤ k') : ρ.τ k ≤ ρ.τ k' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (τ_mono ρ hρ _)

theorem D_finite (k : ℕ) : (ρ.D k).Finite := by
  obtain ⟨f, hf⟩ := inf_of_top ρ hρ
  have := ρ.finite k (f k) (by simp [hf, Seq.get?])
  simpa [Trace.D, hf, Seq.get?] using this

omit hρ in
theorem D_noLet (k : ℕ) (hadm : Admissible (NewNames U.Ξ U.L.lets) ρ) :
    ∀ ev ∈ ρ.D k, ¬ IsLet U.L.lets ev.e :=
  fun ev hev h => hadm k ev hev (Or.inl (Or.inl h))

theorem proRange_eq (k : ℕ) : Enforcer.proRange ρ k = List.range' (ρ.τ k) (ρ.τ (k + 1) - ρ.τ k) := by
  unfold Enforcer.proRange; rw [if_pos (by rw [hρ]; exact ENat.coe_lt_top _)]

include hadm in
/-- **One iteration** of the outer loop of Algorithm 1. -/
theorem RInv.iter (k : ℕ) {st : EState Voc} {σ : Trace Voc.toSignature}
    {l : List (ℕ × DB Voc.toSignature)} (hI : U.RInv st σ l (ρ.τ k)) :
    ∃ st' σ' l', (E U).iter ρ k (some st, σ) = some (some st', σ') ∧
      U.RInv st' σ' l' (ρ.τ (k + 1)) ∧ st.Ω ⊆ st'.Ω ∧ l <+: l' ∧ l.length < l'.length ∧
      ∀ j (hj : j < l'.length), l.length ≤ j → ρ.τ k ≤ l'[j].1 := by
  obtain ⟨st1, C', S', hμ, σ1, hs, hI1, hΩ1⟩ := hI.muStep (D_finite ρ hρ k) (D_noLet ρ k hadm)
    (fun ev hev h => hadm k ev hev (by rcases h with h | h; exact Or.inl (Or.inr h); exact Or.inr h))
  obtain ⟨st', σ', l', h1, h2, h3, h4, h5⟩ := RInv.proLoop (ρ.τ (k + 1) - ρ.τ k) (ρ.τ k) hI1
  have hk := τ_mono ρ hρ k
  refine ⟨st', σ', l', ?_, by rw [show ρ.τ k + (ρ.τ (k + 1) - ρ.τ k) = ρ.τ (k + 1) by omega] at h2; exact h2,
    hΩ1.trans h3, (List.prefix_append l _).trans h4, ?_, fun j hj h => ?_⟩
  · simp only [Enforcer.iter, hμ, hs, Option.bind_some, proRange_eq ρ hρ]; exact h1
  · have := h4.length_le; simp at this; omega
  · by_cases hj' : j = l.length
    · subst hj'
      obtain ⟨u, hu⟩ := h4
      have : l'[l.length] = (l ++ [(ρ.τ k, (ρ.D k \ S'.1) ∪ C'.1)])[l.length]'(by simp) := by
        simp only [← hu]; rw [List.getElem_append_left]
      rw [this]; simp
    · exact h5 j hj (by simp; omega)

include hadm in
/-- **The run of Algorithm 1** never fails. -/
theorem run_inv : ∀ k, ∃ st σ l, (E U).run ρ k = some (some st, σ) ∧ U.RInv st σ l (ρ.τ k) ∧
    k ≤ l.length
  | 0 => ⟨EState.init, Trace.empty, [], rfl, RInv.init U _, le_rfl⟩
  | k + 1 => by
    obtain ⟨st, σ, l, h1, h2, h3⟩ := run_inv k
    obtain ⟨st', σ', l', g1, g2, -, -, g5, -⟩ := RInv.iter ρ hρ hadm k h2
    exact ⟨st', σ', l', by simp only [Enforcer.run, h1, Option.bind_some]; exact g1, g2, by omega⟩

include hadm in
/-- Later states extend earlier ones. -/
theorem run_later {K : ℕ} {st : EState Voc} {σ : Trace Voc.toSignature}
    {l : List (ℕ × DB Voc.toSignature)} (h : (E U).run ρ K = some (some st, σ))
    (hI : U.RInv st σ l (ρ.τ K)) :
    ∀ d {st' : EState Voc} {σ' : Trace Voc.toSignature} {l' : List (ℕ × DB Voc.toSignature)},
      (E U).run ρ (K + d) = some (some st', σ') → U.RInv st' σ' l' (ρ.τ (K + d)) →
      st.Ω ⊆ st'.Ω ∧ l <+: l' ∧ ∀ j (hj : j < l'.length), l.length ≤ j → ρ.τ K ≤ l'[j].1
  | 0, st', σ', l', h', hI' => by
    rw [Nat.add_zero, h] at h'
    injection h' with h''
    injection h'' with e1 e2
    injection e1 with e1
    subst e1 e2
    rw [Nat.add_zero] at hI'
    have hl : l = l' := by have := hI.seq.symm.trans hI'.seq; injection this
    subst hl
    exact ⟨le_rfl, List.prefix_refl _, fun j hj h => by omega⟩
  | d + 1, st', σ', l', h', hI' => by
    obtain ⟨st1, σ1, l1, h1, h2, -⟩ := run_inv ρ hρ hadm (K + d)
    obtain ⟨i1, i2, i3⟩ := run_later h hI d h1 h2
    obtain ⟨st2, σ2, l2, g1, g2, g3, g4, -, g6⟩ := RInv.iter ρ hρ hadm (K + d) h2
    have : (E U).run ρ (K + (d + 1)) = some (some st2, σ2) := by
      rw [← add_assoc]; simp only [Enforcer.run, h1, Option.bind_some]; exact g1
    rw [this] at h'
    injection h' with h''
    injection h'' with e1 e2
    injection e1 with e1
    subst e1 e2
    have hl : l2 = l' := by have := g2.seq.symm.trans hI'.seq; injection this
    subst hl
    refine ⟨i1.trans g3, i2.trans g4, fun j hj h => ?_⟩
    by_cases hj1 : j < l1.length
    · obtain ⟨u, hu⟩ := g4
      have : l2[j] = (l1 ++ u)[j]'(by rw [hu]; exact hj) := by simp only [hu]
      rw [this, List.getElem_append_left hj1]; exact i3 j hj1 h
    · exact le_trans (τ_mono' ρ hρ (by omega)) (g6 j hj (by omega))

end Input

end Setup

end Paper
