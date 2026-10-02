/-
  `Interp` of the compiled program on a history.
-/
import Paper.Proof.Corr

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem mem_withSections (rk : Voc.ℰ → ℕ) :
    ∀ (cur : Option ℕ) (l : List (EClause Voc × Item Voc)) (it : Item Voc),
      it ∈ withSections rk cur l → it = .sec .fixpoint ∨ ∃ p ∈ l, it = p.2
  | _, [], it, h => by simp [withSections] at h
  | cur, (c, it') :: rest, it, h => by
    simp only [withSections] at h
    split_ifs at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr ⟨(c, it), by simp, rfl⟩
      · rcases mem_withSections rk _ rest it h with h | ⟨p, hp, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨p, by simp [hp], rfl⟩
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl rfl
      rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr ⟨(c, it), by simp, rfl⟩
      · rcases mem_withSections rk _ rest it h with h | ⟨p, hp, rfl⟩
        · exact Or.inl h
        · exact Or.inr ⟨p, by simp [hp], rfl⟩

theorem defs_aux (Ξ : RwSetting Voc) (Γ : LetCtx Voc) (colTy : Voc.𝕍 → Ty) :
    ∀ {ℒ : List (LetDef Voc)} {its : List (Item Voc)},
      List.Forall₂ (fun d it => LetItemSpec Ξ Γ colTy d it) ℒ its →
      List.Forall₂ (fun d p => p.1 = d.e ∧ LetItemSpec Ξ Γ colTy d p.2) ℒ
        (its.filterMap fun d => d.defName?.map (·, d))
  | [], [], .nil => .nil
  | d :: ℒ, it :: its, .cons h hs => by
    simp only [List.filterMap_cons, h.defName.1, Option.map_some]
    exact .cons ⟨rfl, h⟩ (defs_aux Ξ Γ colTy hs)

namespace Setup
variable (U : Setup Voc)

theorem prog_spec : ∃ rules : List (EClause Voc × Item Voc),
    List.Forall₂ (fun d p => p.1 = d.e ∧ LetItemSpec U.Ξ U.T.Γ U.colTy d p.2) U.L.lets U.P.defs ∧
    List.Forall₂ (fun c p => p.1 = c ∧ RuleSpec c p.2) U.sorted rules ∧
    U.P.sections = (groupByRk U.rk rules).map toSec := by
  obtain ⟨its, rules, hits, hrules, hP⟩ := U.compile_spec
  refine ⟨rules, ?_, hrules, ?_⟩
  · unfold Program.defs
    rw [hP, List.filterMap_append]
    have hws : (withSections U.rk none rules).filterMap
        (fun d => d.defName?.map (·, d)) = [] := by
      rw [List.filterMap_eq_nil_iff]
      intro it hit
      rcases mem_withSections U.rk none rules it hit with rfl | ⟨p, hp, rfl⟩
      · rfl
      · obtain ⟨c, hc, hcp⟩ := forall₂_mem_right hrules p hp
        simp [hcp.2.defName]
    rw [hws, List.append_nil]
    exact defs_aux U.Ξ U.T.Γ U.colTy hits
  · unfold Program.sections
    rw [hP, sectionsAux_skip]
    · exact sections_withSections U.rk rules fun p hp => by
        obtain ⟨c, hc, hcp⟩ := forall₂_mem_right hrules p hp
        exact hcp.2.isRule
    · intro it hit
      obtain ⟨d, hd, h⟩ := forall₂_mem_right hits it hit
      exact ⟨h.defName.2.1, h.defName.2.2⟩

/-- A set of rows that are well-typed, non-let events. -/
def Good (X : Set (REv Voc)) : Prop :=
  ∀ x ∈ X, x.2.length = Voc.ι x.1 ∧ ¬ IsLet U.L.lets x.1

theorem tablesOf_let (H : List (ℕ × DB Voc.toSignature)) {d : LetDef Voc} (hd : d ∈ U.L.lets) :
    TablesOf U.L.lets H d.e = TabFor U.L.lets H d := by
  ext tr; simp only [TablesOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨d', hd', he, h⟩
    rwa [List.inj_on_of_nodup_map U.wf.nodup hd' hd he] at h
  · intro h; exact ⟨d, hd, rfl, h⟩

theorem tablesOf_base (H : List (ℕ × DB Voc.toSignature)) {q : Voc.ℰ} (hq : ¬ IsLet U.L.lets q) :
    TablesOf U.L.lets H q = ∅ := by
  ext tr; simp only [TablesOf, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    not_and]
  intro d hd he; exact absurd ⟨d, hd, he⟩ hq

theorem toDB_mem {X : Set (REv Voc)} {ev : Event Voc.toSignature} :
    ev ∈ REv.toDB X ↔ (ev.e, ev.args) ∈ X := Iff.rfl

theorem good_noLet {X : Set (REv Voc)} (hX : U.Good X) (H : List (ℕ × DB Voc.toSignature))
    (hH : ∀ m (hm : m < H.length), ∀ ev ∈ H[m].2, ¬ IsLet U.L.lets ev.e) (τ : ℕ) :
    ∀ j, ∀ ev ∈ (strOf H τ (REv.toDB X)).D j, ¬ IsLet U.L.lets ev.e := by
  intro j ev hev
  simp only [strOf] at hev
  split_ifs at hev with h1 h2
  · exact hH j h1 ev hev
  · exact (hX _ hev).2
  · exact absurd hev (Set.notMem_empty _)

/-- **`Interp(𝒮)` is the let semantics** of the history extended by the
    events of `𝒮`. -/
theorem interp_corr (H : List (ℕ × DB Voc.toSignature)) (W : WorkingSet Voc)
    (hH : ∀ m (hm : m < H.length), ∀ ev ∈ H[m].2, ¬ IsLet U.L.lets ev.e)
    (hX : U.Good ((W.D \ W.S) ∪ W.C)) (hmono : ∀ m (hm : m < H.length), H[m].1 ≤ W.τ)
    (hT : ∀ q, W.T q = TablesOf U.L.lets H q ∨
      ((∀ d ∈ U.L.lets, d.e = q → ∀ I φ, d.φ ≠ .prev I φ) ∧
        W.T q = TablesOf U.L.lets (H ++ [(W.τ, REv.toDB ((W.D \ W.S) ∪ W.C))]) q)) :
    ∀ q, Interp U.P W q = RelOf (U.SA H W.τ (REv.toDB ((W.D \ W.S) ∪ W.C))) H.length q := by
  set X := (W.D \ W.S) ∪ W.C
  set S := U.SA H W.τ (REv.toDB X)
  set j := H.length
  set ℒ := U.L.lets
  have h₀ := U.good_noLet hX H hH W.τ
  have hmono' : ∀ m ≤ H.length, (strOf H W.τ (REv.toDB X)).τ m ≤ W.τ := by
    intro m hm
    rcases Nat.lt_or_eq_of_le hm with hm | rfl
    · rw [strOf_τ_lt _ _ _ hm]; exact hmono m hm
    · rw [strOf_τ_len]
  have hAL := applyLets_spec' ℒ U.wf.nodup U.scope_names _ h₀ ℒ.length le_rfl
  rw [List.take_length] at hAL
  obtain ⟨-, hbase, -⟩ := hAL
  -- the base interpretation is right on non-let names
  set R₀ : Interpretation Voc := fun p => {r | (p, r) ∈ X}
  have hR₀ : ∀ q, ¬ IsLet ℒ q → R₀ q = RelOf S j q := by
    intro q hq
    ext r
    simp only [R₀, Set.mem_setOf_eq, RelOf]
    constructor
    · intro h
      have hlen := (hX _ h).1
      refine ⟨⟨q, r, hlen⟩, ?_, rfl, rfl⟩
      rw [show S = applyLets ℒ (strOf H W.τ (REv.toDB X)) from rfl,
        hbase j _ fun k hk _ he => hq ⟨ℒ[k], List.getElem_mem hk, he.symm⟩, strOf_D_len]
      exact h
    · rintro ⟨ev, hev, rfl, rfl⟩
      rw [show S = applyLets ℒ (strOf H W.τ (REv.toDB X)) from rfl,
        hbase j _ fun k hk _ he => hq ⟨ℒ[k], List.getElem_mem hk, he.symm⟩, strOf_D_len] at hev
      exact hev
  obtain ⟨rules, hdefs, -, -⟩ := U.prog_spec
  have hlen : U.P.defs.length = ℒ.length := (List.Forall₂.length_eq hdefs).symm
  let step : Interpretation Voc → Voc.ℰ × Item Voc → Interpretation Voc :=
    fun R d => Function.update R d.1 (Eval d.2 R W.T W.τ)
  -- induction over the definitions
  have key : ∀ n ≤ ℒ.length,
      (∀ q, ¬ IsLet ℒ q → ((U.P.defs.take n).foldl step R₀) q = R₀ q) ∧
      ∀ k (hk : k < ℒ.length), k < n → ((U.P.defs.take n).foldl step R₀) ℒ[k].e = RelOf S j ℒ[k].e := by
    intro n
    induction n with
    | zero => intro _; exact ⟨fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn
      obtain ⟨i1, i2⟩ := ih (by omega)
      have hnl : n < ℒ.length := by omega
      have hdn := List.Forall₂.get hdefs hnl (by omega)
      simp only [List.get_eq_getElem] at hdn
      rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      set Rn := (U.P.defs.take n).foldl step R₀
      have hname : U.P.defs[n].1 = ℒ[n].e := hdn.1
      have hEval : Eval U.P.defs[n].2 Rn W.T W.τ = RelOf S j ℒ[n].e := by
        refine U.eval_corr (List.getElem_mem hnl) hdn.2 H W.τ (REv.toDB X) h₀ hmono' Rn W.T ?_ ?_
        · intro q hq
          rcases U.scope_names n hnl q (by
            rw [Formula.names_eq_preds (IsLetBody.noLet (U.lets_body _ (List.getElem_mem hnl)))]
            exact hq) with hq' | ⟨k', hk', hk'l, rfl⟩
          · rw [i1 q hq', hR₀ q hq']
          · exact i2 k' hk'l hk'
        · rcases hT ℒ[n].e with h | ⟨hl, h⟩
          · left; rw [h, U.tablesOf_let _ (List.getElem_mem hnl)]
          · right; exact ⟨hl _ (List.getElem_mem hnl) rfl, by rw [h, U.tablesOf_let _ (List.getElem_mem hnl)]⟩
      refine ⟨fun q hq => ?_, fun k hk hkn => ?_⟩
      · simp only [step]
        rw [Function.update_of_ne (by rw [hname]; exact fun h => hq ⟨ℒ[n], List.getElem_mem hnl, h.symm⟩)]
        exact i1 q hq
      · simp only [step]
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hkn) with hlt | rfl
        · rw [Function.update_of_ne (by
            rw [hname]; intro h; exact absurd (names_inj U.wf.nodup hk hnl h) (by omega))]
          exact i2 k hk hlt
        · rw [hname, Function.update_self, hEval]
  obtain ⟨k1, k2⟩ := key ℒ.length le_rfl
  have htake : U.P.defs.take ℒ.length = U.P.defs := by rw [← hlen, List.take_length]
  simp only [htake] at k1 k2
  intro q
  have hI : Interp U.P W = U.P.defs.foldl step R₀ := rfl
  rw [hI]
  by_cases hq : IsLet ℒ q
  · obtain ⟨d, hd, rfl⟩ := hq
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    exact k2 k hk hk
  · rw [k1 q hq, hR₀ q hq]

end Setup

end Paper
