/-
  The table updates of `Saturate` compute the tables of the extended history.
-/
import Paper.Proof.Interp

namespace Paper

open Classical

variable {Voc : Vocabulary}

namespace Setup
variable (U : Setup Voc)

/-- The context of one time-point: the history `H` and the final sets of the
    working set. -/
structure PtCtx (U : Setup Voc) where
  H : List (ℕ × DB Voc.toSignature)
  τ : ℕ
  D : Set (REv Voc)
  C : Set (REv Voc)
  S : Set (REv Voc)
  hH : ∀ m (hm : m < H.length), ∀ ev ∈ H[m].2, ¬ IsLet U.L.lets ev.e
  hX : U.Good ((D \ S) ∪ C)
  hmono : ∀ m (hm : m < H.length), H[m].1 ≤ τ

namespace PtCtx
variable {U} (K : PtCtx U)

/-- The current time-point. -/
def pt : ℕ × DB Voc.toSignature := (K.τ, REv.toDB ((K.D \ K.S) ∪ K.C))

/-- The let structure. -/
noncomputable def St : Str Voc.toSignature := U.SA K.H K.τ (REv.toDB ((K.D \ K.S) ∪ K.C))

theorem interp (T : Tables Voc)
    (hT : ∀ q, T q = TablesOf U.L.lets K.H q ∨
      ((∀ d ∈ U.L.lets, d.e = q → ∀ I φ, d.φ ≠ .prev I φ) ∧
        T q = TablesOf U.L.lets (K.H ++ [K.pt]) q)) :
    ∀ q, Interp U.P ⟨T, K.τ, K.D, K.C, K.S⟩ q = RelOf K.St K.H.length q :=
  U.interp_corr K.H ⟨T, K.τ, K.D, K.C, K.S⟩ K.hH K.hX K.hmono hT

end PtCtx

theorem rows_corr {R : Interpretation Voc} {S : Str Voc.toSignature} {j : ℕ}
    (hR : ∀ q, R q = RelOf S j q) {m : Set Voc.ℰ} {X : Set Voc.𝕍} {Φ : Formula Voc}
    {a : Clause Voc} (ha : GuardClause m X Φ a) (hX : Φ.fv ⊆ X) {xs : List Voc.𝕍}
    (hXxs : X = {x | x ∈ xs}) : rows R a xs = RowsAt S j Φ xs := by
  rw [rows_guard ha hX (fun q _ => hR q), hXxs, rows_dom_eq (hXxs ▸ hX)]

theorem rowsAt_not_neg {S : Str Voc.toSignature} {m : ℕ} {φ : Formula Voc} {xs : List Voc.𝕍}
    (hfv : φ.fv ⊆ {x | x ∈ xs}) (hnd : xs.Nodup) {r : List Voc.𝔻} (hr : r.length = xs.length) :
    r ∉ RowsAt S m (.neg φ) xs ↔ r ∈ RowsAt S m φ xs := by
  obtain ⟨v, hv, -⟩ := val_of_args xs r hnd hr.symm
  rw [rowsAt_iff (φ := .neg φ) hfv hv, rowsAt_iff hfv hv]; simp [Formula.sat]

/-- The new content of a `Since` table. -/
theorem since_update (K : U.PtCtx) {d : LetDef Voc} (hd : d ∈ U.L.lets) {I : Interval}
    {φl φr : Formula Voc} (hφ : d.φ = .since I φl φr) (Rem : Set (List Voc.𝔻))
    (hRem : ∀ r, r.length = d.xs.length → (r ∈ Rem ↔ r ∉ RowsAt K.St K.H.length φl d.xs))
    (Add : Set (List Voc.𝔻)) (hAdd : Add = RowsAt K.St K.H.length φr d.xs) :
    (TabFor U.L.lets K.H d \ {tr | ∃ rr, rr ∈ Rem ∧ tr.2 = rr}) ∪ {tr | tr.1 = K.τ ∧ tr.2 ∈ Add} =
      TabFor U.L.lets (K.H ++ [K.pt]) d := by
  have hp := U.pastF d hd
  obtain ⟨h1, h2⟩ := U.tabFor_since K.H K.τ (REv.toDB ((K.D \ K.S) ∪ K.C)) hφ hp
  simp only [PtCtx.pt, PtCtx.St] at hRem hAdd ⊢
  rw [h1, h2]
  set S := U.SA K.H K.τ (REv.toDB ((K.D \ K.S) ∪ K.C))
  have hSτ : S.τ K.H.length = K.τ := by rw [U.SA_τ, strOf_τ_len]
  subst hAdd
  ext ⟨t, r⟩
  simp only [Set.mem_union, Set.mem_diff, Set.mem_setOf_eq, not_exists, not_and]
  constructor
  · rintro (⟨⟨m, hm, rfl, hr, hl⟩, hnot⟩ | ⟨rfl, hr⟩)
    · refine ⟨m, by omega, rfl, hr, fun m' a b => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ b) with b | rfl
      · exact hl m' a b
      · by_contra hc
        exact hnot r ((hRem r (rowsAt_len hr)).2 hc) rfl
    · exact ⟨K.H.length, by omega, by rw [hSτ], hr, fun m' a b => absurd b (by omega)⟩
  · rintro ⟨m, hm, rfl, hr, hl⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm | rfl
    · left
      refine ⟨⟨m, hm, rfl, hr, fun m' a b => hl m' a (by omega)⟩, fun rr hrr heq => ?_⟩
      subst heq
      exact (hRem _ (rowsAt_len hr)).1 hrr (hl K.H.length hm (by omega))
    · right; exact ⟨hSτ.symm ▸ rfl, hr⟩

/-- The content of a lagged table. -/
theorem prev_update (K : U.PtCtx) {d : LetDef Voc} (hd : d ∈ U.L.lets) {I : Interval}
    {φ : Formula Voc} (hφ : d.φ = .prev I φ) :
    {tr | tr.1 = K.τ ∧ tr.2 ∈ RowsAt K.St K.H.length φ d.xs} =
      TabFor U.L.lets (K.H ++ [K.pt]) d := by
  have hp := U.pastF d hd
  have h := U.tabFor_prev (K.H ++ [K.pt]) K.τ ∅ hφ hp
  rw [h]
  simp only [PtCtx.St]
  have hP := U.SA_snoc_past K.H K.τ (REv.toDB ((K.D \ K.S) ∪ K.C))
  have hP' : PastAgree (U.SA K.H K.τ (REv.toDB ((K.D \ K.S) ∪ K.C))) (U.SA (K.H ++ [K.pt]) K.τ ∅)
      K.H.length := by
    intro k hk
    have h1 := hP k hk
    have h2 := U.SA_past (K.H ++ [K.pt]) K.τ ∅ (m := k) (by simp; omega) k le_rfl
    exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
  ext ⟨t, r⟩
  simp only [Set.mem_setOf_eq, List.length_append, List.length_singleton, Nat.add_right_cancel_iff,
    exists_eq_left]
  rw [rowsAt_past hP' le_rfl (φ := φ) (by rw [hφ] at hp; exact hp)]
  have hτ : (U.SA (K.H ++ [K.pt]) K.τ ∅).τ K.H.length = K.τ := by
    rw [U.SA_τ, strOf_τ_lt _ _ _ (by simp)]; simp [PtCtx.pt]
  rw [hτ]

/-- Which lets are tables. -/
def IsSince (d : LetDef Voc) : Prop := ∃ I φl φr, d.φ = .since I φl φr

theorem tabFor_other {d : LetDef Voc} (h1 : ¬ IsSince d) (h2 : ∀ I φ, d.φ ≠ .prev I φ)
    (H : List (ℕ × DB Voc.toSignature)) : TabFor U.L.lets H d = ∅ := by
  unfold TabFor
  split
  · rename_i I φl φr heq; exact absurd ⟨I, φl, φr, heq⟩ h1
  · rename_i I φ heq; exact absurd heq (h2 I φ)
  · rfl

section folds
variable (K : U.PtCtx)

/-- The tables during the updates: each table holds its content after the history,
    or (for a `Since` table) after the history and the current time-point. -/
def TGood (T : Tables Voc) : Prop :=
  ∀ q, T q = TablesOf U.L.lets K.H q ∨
    ((∀ d ∈ U.L.lets, d.e = q → IsSince d) ∧ T q = TablesOf U.L.lets (K.H ++ [K.pt]) q)

theorem TGood.interp {K : U.PtCtx} {T : Tables Voc} (h : U.TGood K T) :
    ∀ q, Interp U.P ⟨T, K.τ, K.D, K.C, K.S⟩ q = RelOf K.St K.H.length q := by
  refine K.interp T fun q => ?_
  rcases h q with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨fun d hd he I φ hφ => ?_, h2⟩
    obtain ⟨I', l, r, h'⟩ := h1 d hd he
    rw [hφ] at h'; cases h'

theorem since_of_spec {d : LetDef Voc} (hd : d ∈ U.L.lets) {it : Item Voc}
    (h : LetItemSpec U.Ξ U.T.Γ U.colTy d it) :
    (IsSince d ↔ ∃ ℓ p cols w a r, it = .table ℓ false p cols w a r) ∧
    ((∃ I φ, d.φ = .prev I φ) ↔ ∃ ℓ p cols w a r, it = .table ℓ true p cols w a r) := by
  have hb := U.lets_body d hd
  cases h with
  | once I φ a hχ ha =>
    have := letBody_since hb hχ
    exact ⟨⟨fun _ => ⟨_, _, _, _, _, _, rfl⟩, fun _ => ⟨_, _, _, this⟩⟩,
      ⟨fun ⟨I', φ', h'⟩ => (by rw [this] at h'; cases h'), fun ⟨_, _, _, _, _, _, h'⟩ => (by cases h')⟩⟩
  | since I φl φr a r hχ _ ha hr =>
    have := letBody_since hb hχ
    exact ⟨⟨fun _ => ⟨_, _, _, _, _, _, rfl⟩, fun _ => ⟨_, _, _, this⟩⟩,
      ⟨fun ⟨I', φ', h'⟩ => (by rw [this] at h'; cases h'), fun ⟨_, _, _, _, _, _, h'⟩ => (by cases h')⟩⟩
  | prev I φ a hχ ha =>
    have := letBody_prev hb hχ
    exact ⟨⟨fun ⟨_, _, _, h'⟩ => (by rw [this] at h'; cases h'), fun ⟨_, _, _, _, _, _, h'⟩ => (by cases h')⟩,
      ⟨fun _ => ⟨_, _, _, _, _, _, rfl⟩, fun _ => ⟨_, _, this⟩⟩⟩
  | agg ys ω ss gs φ a hχ _ _ ha =>
    have := letBody_agg hb hχ
    exact ⟨⟨fun ⟨_, _, _, h'⟩ => (by rw [this] at h'; cases h'), fun ⟨_, _, _, _, _, _, h'⟩ => (by cases h')⟩,
      ⟨fun ⟨_, _, h'⟩ => (by rw [this] at h'; cases h'), fun ⟨_, _, _, _, _, _, h'⟩ => (by cases h')⟩⟩
  | filt f h1 h2 h3 _ _ =>
    refine ⟨⟨fun ⟨I, l, r, h'⟩ => ?_, fun ⟨_, _, _, _, _, _, h'⟩ => (by cases h')⟩,
      ⟨fun ⟨I, φ, h'⟩ => ?_, fun ⟨_, _, _, _, _, _, h'⟩ => (by cases h')⟩⟩
    · exact absurd (by rw [h']; rfl) (h1 I l r)
    · exact absurd (by rw [h']; rfl) (h2 I φ)
  | plet a h1 h2 h3 _ _ =>
    refine ⟨⟨fun ⟨I, l, r, h'⟩ => ?_, fun ⟨_, _, _, _, _, _, h'⟩ => (by cases h')⟩,
      ⟨fun ⟨I, φ, h'⟩ => ?_, fun ⟨_, _, _, _, _, _, h'⟩ => (by cases h')⟩⟩
    · exact absurd (by rw [h']; rfl) (h1 I l r)
    · exact absurd (by rw [h']; rfl) (h2 I φ)

/-- One `updTable` step. -/
theorem updTable_step {d : LetDef Voc} (hd : d ∈ U.L.lets) {it : Item Voc}
    (h : LetItemSpec U.Ξ U.T.Γ U.colTy d it) {T : Tables Voc} (hT : U.TGood K T)
    (hTd : T d.e = TablesOf U.L.lets K.H d.e) :
    (IsSince d → updTable U.P K.τ K.D K.C K.S T it =
        Function.update T d.e (TablesOf U.L.lets (K.H ++ [K.pt]) d.e)) ∧
      (¬ IsSince d → updTable U.P K.τ K.D K.C K.S T it = T) := by
  have hR := hT.interp
  have hb := U.lets_body d hd
  have hnd := U.wf.nodup_xs d hd
  have hfvd := U.wf.fv_let d hd
  rw [U.tablesOf_let _ hd] at hTd
  cases h with
  | once I φ a hχ ha =>
    have hφ := letBody_since hb hχ
    have hfvφ : φ.fv = {x | x ∈ d.xs} := by rw [← hfvd, hφ]; simp [Formula.fv]
    refine ⟨fun _ => ?_, fun hn => absurd ⟨_, _, _, hφ⟩ hn⟩
    unfold updTable; dsimp only; rw [letCols_names U.T.Γ]
    congr 1
    rw [hTd, rows_corr hR ha le_rfl hfvφ, U.tablesOf_let _ hd]
    refine U.since_update K hd hφ _ (fun r hr => ?_) _ rfl
    obtain ⟨v, hv, -⟩ := val_of_args d.xs r hnd hr.symm
    have hin : r ∈ RowsAt K.St K.H.length .top d.xs := ⟨v, covers_of_map hv, hv, trivial⟩
    constructor
    · intro h; exact h.elim
    · intro h; exact absurd hin h
  | since I φl φr a r hχ _ ha hr =>
    have hφ := letBody_since hb hχ
    have hfvs : (Formula.since I φl φr).fv = {x | x ∈ d.xs} := by rw [← hφ, hfvd]
    have hfvl : φl.fv ⊆ {x | x ∈ d.xs} := by rw [← hfvs]; exact Set.subset_union_left
    have hfvr : φr.fv ⊆ {x | x ∈ d.xs} := by rw [← hfvs]; exact Set.subset_union_right
    have hX : ({x | x ∈ d.xs} ∪ (stripExists d.φ).fv : Set Voc.𝕍) = {x | x ∈ d.xs} := by
      rw [hχ, hfvs, Set.union_self]
    rw [hX] at ha hr
    refine ⟨fun _ => ?_, fun hn => absurd ⟨_, _, _, hφ⟩ hn⟩
    unfold updTable; dsimp only; rw [letCols_names U.T.Γ]
    congr 1
    rw [hTd, rows_corr hR ha hfvr rfl, U.tablesOf_let _ hd]
    refine U.since_update K hd hφ _ (fun r' hr' => ?_) _ rfl
    change r' ∈ rows _ r d.xs ↔ _
    rw [rows_corr hR hr (Φ := .neg φl) hfvl rfl]
    have := rowsAt_not_neg (S := K.St) (m := K.H.length) hfvl hnd hr'
    exact ⟨fun h1 h2 => (this.2 h2) h1, fun h1 => by_contra fun h2 => h1 (this.1 h2)⟩
  | prev I φ a hχ ha =>
    refine ⟨fun ⟨I', l, r, h'⟩ => (by rw [letBody_prev hb hχ] at h'; cases h'), fun _ => rfl⟩
  | agg ys ω ss gs φ a hχ _ _ ha =>
    refine ⟨fun ⟨I', l, r, h'⟩ => (by rw [letBody_agg hb hχ] at h'; cases h'), fun _ => rfl⟩
  | filt f h1 h2 h3 _ _ =>
    refine ⟨fun ⟨I', l, r, h'⟩ => absurd (by rw [h']; rfl) (h1 I' l r), fun _ => rfl⟩
  | plet a h1 h2 h3 _ _ =>
    refine ⟨fun ⟨I', l, r, h'⟩ => absurd (by rw [h']; rfl) (h1 I' l r), fun _ => rfl⟩

/-- One `updLagged` step (with the tables `T` fixed, as fixed in S5). -/
theorem updLagged_step {d : LetDef Voc} (hd : d ∈ U.L.lets) {it : Item Voc}
    (h : LetItemSpec U.Ξ U.T.Γ U.colTy d it) {T : Tables Voc} (hT : U.TGood K T)
    (TT : Tables Voc × Tables Voc) :
    ((∃ I φ, d.φ = .prev I φ) → updLagged U.P K.τ K.D K.C K.S T TT it =
        (Function.update TT.1 d.e (TablesOf U.L.lets (K.H ++ [K.pt]) d.e),
          Function.update TT.2 d.e (TablesOf U.L.lets (K.H ++ [K.pt]) d.e))) ∧
      ((¬ ∃ I φ, d.φ = .prev I φ) → updLagged U.P K.τ K.D K.C K.S T TT it = TT) := by
  have hR := hT.interp
  have hb := U.lets_body d hd
  have hfvd := U.wf.fv_let d hd
  cases h with
  | prev I φ a hχ ha =>
    have hφ := letBody_prev hb hχ
    have hfvφ : φ.fv = {x | x ∈ d.xs} := by rw [← hfvd, hφ]; simp [Formula.fv]
    refine ⟨fun _ => ?_, fun hn => absurd ⟨_, _, hφ⟩ hn⟩
    unfold updLagged; dsimp only; rw [letCols_names U.T.Γ, rows_corr hR ha le_rfl hfvφ,
      U.prev_update K hd hφ, U.tablesOf_let _ hd, Function.update_self]
  | once I φ a hχ ha =>
    exact ⟨fun ⟨I', φ', h'⟩ => (by rw [letBody_since hb hχ] at h'; cases h'), fun _ => rfl⟩
  | since I φl φr a r hχ _ ha hr =>
    exact ⟨fun ⟨I', φ', h'⟩ => (by rw [letBody_since hb hχ] at h'; cases h'), fun _ => rfl⟩
  | agg ys ω ss gs φ a hχ _ _ ha =>
    exact ⟨fun ⟨I', φ', h'⟩ => (by rw [letBody_agg hb hχ] at h'; cases h'), fun _ => rfl⟩
  | filt f h1 h2 h3 _ _ =>
    exact ⟨fun ⟨I', φ', h'⟩ => absurd (by rw [h']; rfl) (h2 I' φ'), fun _ => rfl⟩
  | plet a h1 h2 h3 _ _ =>
    exact ⟨fun ⟨I', φ', h'⟩ => absurd (by rw [h']; rfl) (h2 I' φ'), fun _ => rfl⟩

theorem updTable_fold : ∀ {ℒ' : List (LetDef Voc)} {its : List (Item Voc)},
    List.Forall₂ (fun d it => LetItemSpec U.Ξ U.T.Γ U.colTy d it) ℒ' its →
    (∀ d ∈ ℒ', d ∈ U.L.lets) → (ℒ'.map LetDef.e).Nodup →
    ∀ T, U.TGood K T → (∀ d ∈ ℒ', T d.e = TablesOf U.L.lets K.H d.e) →
      let T' := its.foldl (updTable U.P K.τ K.D K.C K.S) T
      U.TGood K T' ∧ (∀ q, (∀ d ∈ ℒ', d.e ≠ q) → T' q = T q) ∧
        (∀ d ∈ ℒ', IsSince d → T' d.e = TablesOf U.L.lets (K.H ++ [K.pt]) d.e) ∧
        (∀ d ∈ ℒ', ¬ IsSince d → T' d.e = T d.e)
  | [], [], .nil, _, _, T, hT, _ => ⟨hT, fun _ _ => rfl, by simp, by simp⟩
  | d :: ℒ', it :: its, .cons h hs, hsub, hnd, T, hT, hTd => by
    have hd : d ∈ U.L.lets := hsub d (by simp)
    have hnd2 := List.nodup_cons.1 (show (d.e :: ℒ'.map LetDef.e).Nodup from hnd)
    have hnd' := hnd2.2
    have hdn : ∀ d' ∈ ℒ', d'.e ≠ d.e := by
      intro d' hd' he
      exact hnd2.1 (by rw [← he]; exact List.mem_map_of_mem hd')
    obtain ⟨hsince, hnot⟩ := U.updTable_step K hd h hT (hTd d (by simp))
    set T₁ := updTable U.P K.τ K.D K.C K.S T it
    have hT₁ : U.TGood K T₁ ∧ (∀ q, q ≠ d.e → T₁ q = T q) ∧
        (IsSince d → T₁ d.e = TablesOf U.L.lets (K.H ++ [K.pt]) d.e) ∧ (¬ IsSince d → T₁ d.e = T d.e) := by
      by_cases hs' : IsSince d
      · rw [show T₁ = _ from hsince hs']
        refine ⟨fun q => ?_, fun q hq => Function.update_of_ne hq _ _, fun _ => by simp, fun h => absurd hs' h⟩
        by_cases hq : q = d.e
        · subst hq; right; refine ⟨fun d' hd' he => ?_, by simp⟩
          rwa [List.inj_on_of_nodup_map U.wf.nodup hd' hd he]
        · rw [Function.update_of_ne hq]; exact hT q
      · rw [show T₁ = T from hnot hs']
        exact ⟨hT, fun _ _ => rfl, fun h => absurd h hs', fun _ => rfl⟩
    obtain ⟨g1, g2, g3, g4⟩ := hT₁
    have ih := updTable_fold hs (fun d' hd' => hsub d' (by simp [hd'])) hnd' T₁ g1
      (fun d' hd' => by rw [g2 _ (hdn d' hd'), hTd d' (by simp [hd'])])
    simp only [List.foldl_cons]
    obtain ⟨i1, i2, i3, i4⟩ := ih
    refine ⟨i1, fun q hq => ?_, fun d' hd' hs' => ?_, fun d' hd' hs' => ?_⟩
    · rw [i2 q fun d' hd' => hq d' (by simp [hd']), g2 q (Ne.symm (hq d (by simp)))]
    · rcases List.mem_cons.1 hd' with rfl | hd'
      · rw [i2 _ (fun d'' hd'' => hdn d'' hd''), g3 hs']
      · exact i3 d' hd' hs'
    · rcases List.mem_cons.1 hd' with rfl | hd'
      · rw [i2 _ (fun d'' hd'' => hdn d'' hd''), g4 hs']
      · rw [i4 d' hd' hs', g2 _ (hdn d' hd')]

theorem updLagged_fold {T : Tables Voc} (hT : U.TGood K T) :
    ∀ {ℒ' : List (LetDef Voc)} {its : List (Item Voc)},
    List.Forall₂ (fun d it => LetItemSpec U.Ξ U.T.Γ U.colTy d it) ℒ' its →
    (∀ d ∈ ℒ', d ∈ U.L.lets) → (ℒ'.map LetDef.e).Nodup →
    ∀ TT : Tables Voc × Tables Voc,
      let TT' := its.foldl (updLagged U.P K.τ K.D K.C K.S T) TT
      (∀ q, (∀ d ∈ ℒ', d.e ≠ q) → TT'.1 q = TT.1 q) ∧
        (∀ d ∈ ℒ', (∃ I φ, d.φ = .prev I φ) → TT'.1 d.e = TablesOf U.L.lets (K.H ++ [K.pt]) d.e) ∧
        (∀ d ∈ ℒ', (¬ ∃ I φ, d.φ = .prev I φ) → TT'.1 d.e = TT.1 d.e)
  | [], [], .nil, _, _, TT => ⟨fun _ _ => rfl, by simp, by simp⟩
  | d :: ℒ', it :: its, .cons h hs, hsub, hnd, TT => by
    have hd : d ∈ U.L.lets := hsub d (by simp)
    have hnd2 := List.nodup_cons.1 (show (d.e :: ℒ'.map LetDef.e).Nodup from hnd)
    have hnd' := hnd2.2
    have hdn : ∀ d' ∈ ℒ', d'.e ≠ d.e := by
      intro d' hd' he
      exact hnd2.1 (by rw [← he]; exact List.mem_map_of_mem hd')
    obtain ⟨hprev, hnot⟩ := U.updLagged_step K hd h hT TT
    set TT₁ := updLagged U.P K.τ K.D K.C K.S T TT it
    have hT₁ : (∀ q, q ≠ d.e → TT₁.1 q = TT.1 q) ∧
        ((∃ I φ, d.φ = .prev I φ) → TT₁.1 d.e = TablesOf U.L.lets (K.H ++ [K.pt]) d.e) ∧
        ((¬ ∃ I φ, d.φ = .prev I φ) → TT₁.1 d.e = TT.1 d.e) := by
      by_cases hp : ∃ I φ, d.φ = .prev I φ
      · rw [show TT₁ = _ from hprev hp]
        exact ⟨fun q hq => Function.update_of_ne hq _ _, fun _ => by simp, fun h => absurd hp h⟩
      · rw [show TT₁ = TT from hnot hp]
        exact ⟨fun _ _ => rfl, fun h => absurd h hp, fun _ => rfl⟩
    obtain ⟨g2, g3, g4⟩ := hT₁
    have ih := updLagged_fold hT hs (fun d' hd' => hsub d' (by simp [hd'])) hnd' TT₁
    simp only [List.foldl_cons]
    obtain ⟨i2, i3, i4⟩ := ih
    refine ⟨fun q hq => ?_, fun d' hd' hs' => ?_, fun d' hd' hs' => ?_⟩
    · rw [i2 q fun d' hd' => hq d' (by simp [hd']), g2 q (Ne.symm (hq d (by simp)))]
    · rcases List.mem_cons.1 hd' with rfl | hd'
      · rw [i2 _ (fun d'' hd'' => hdn d'' hd''), g3 hs']
      · exact i3 d' hd' hs'
    · rcases List.mem_cons.1 hd' with rfl | hd'
      · rw [i2 _ (fun d'' hd'' => hdn d'' hd''), g4 hs']
      · rw [i4 d' hd' hs', g2 _ (hdn d' hd')]

theorem foldl_id {α β : Type} {f : α → β → α} : ∀ (l : List β), (∀ b ∈ l, ∀ x, f x b = x) →
    ∀ x, l.foldl f x = x
  | [], _, x => rfl
  | b :: l, h, x => by
    simp only [List.foldl_cons, h b (by simp) x]; exact foldl_id l (fun b' hb' => h b' (by simp [hb'])) x

/-- **The tables after a time-point** are those of the extended history. -/
theorem tables_final (TN : Tables Voc) :
    (U.P.items.foldl (updLagged U.P K.τ K.D K.C K.S
        (U.P.items.foldl (updTable U.P K.τ K.D K.C K.S) (TablesOf U.L.lets K.H)))
      (U.P.items.foldl (updTable U.P K.τ K.D K.C K.S) (TablesOf U.L.lets K.H), TN)).1 =
      TablesOf U.L.lets (K.H ++ [K.pt]) := by
  obtain ⟨its, rules, hits, hrules, hP⟩ := U.compile_spec
  have hws : ∀ it ∈ withSections U.rk none rules, (∀ T, updTable U.P K.τ K.D K.C K.S T it = T) ∧
      ∀ T TT, updLagged U.P K.τ K.D K.C K.S T TT it = TT := by
    intro it hit
    rcases mem_withSections U.rk none rules it hit with rfl | ⟨p, hp, rfl⟩
    · exact ⟨fun _ => rfl, fun _ _ => rfl⟩
    · obtain ⟨c, -, -, hc⟩ := forall₂_mem_right hrules p hp
      generalize p.2 = it' at hc ⊢
      cases hc <;> exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  have e1 : ∀ T, (withSections U.rk none rules).foldl (updTable U.P K.τ K.D K.C K.S) T = T :=
    foldl_id _ (fun it hit => (hws it hit).1)
  have e2 : ∀ T TT, (withSections U.rk none rules).foldl (updLagged U.P K.τ K.D K.C K.S T) TT = TT :=
    fun T => foldl_id _ (fun it hit => (hws it hit).2 T)
  rw [hP]
  simp only [List.foldl_append, e1, e2]
  have hT₀ : U.TGood K (TablesOf U.L.lets K.H) := fun q => Or.inl rfl
  obtain ⟨g1, g2, g3, g4⟩ := U.updTable_fold K hits (fun d hd => hd) U.wf.nodup _ hT₀
    (fun _ _ => rfl)
  set T₁ := its.foldl (updTable U.P K.τ K.D K.C K.S) (TablesOf U.L.lets K.H)
  obtain ⟨i2, i3, i4⟩ := U.updLagged_fold K g1 hits (fun d hd => hd) U.wf.nodup (T₁, TN)
  funext q
  by_cases hq : IsLet U.L.lets q
  · obtain ⟨d, hd, rfl⟩ := hq
    by_cases hp : ∃ I φ, d.φ = .prev I φ
    · exact i3 d hd hp
    · rw [i4 d hd hp]
      show T₁ d.e = _
      by_cases hs : IsSince d
      · exact g3 d hd hs
      · rw [g4 d hd hs, U.tablesOf_let _ hd, U.tablesOf_let _ hd,
          U.tabFor_other hs (fun I φ h => hp ⟨I, φ, h⟩), U.tabFor_other hs (fun I φ h => hp ⟨I, φ, h⟩)]
  · have hn : ∀ d ∈ U.L.lets, d.e ≠ q := fun d hd he => hq ⟨d, hd, he⟩
    rw [i2 q hn]; simp only
    rw [g2 q hn, U.tablesOf_base _ hq, U.tablesOf_base _ hq]

end folds

end Setup

end Paper
