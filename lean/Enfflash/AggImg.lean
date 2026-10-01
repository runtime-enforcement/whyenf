/-
  EnfFlash formalization — values produced by aggregations.

  An aggregation `ȳ ← ω(t̄; ḡ) φ` computes new values: the results of `ω` on
  the multiset of rows `t̄` over the valuations satisfying `φ`.  If all these
  valuations take values in a finite set `U`, the rows range over a finite
  set and their multiplicities are bounded, so only finitely many multisets,
  hence finitely many results, are possible (`aggImg_finite`).

  `aggClo Γ n U`: the values obtained from `U` by at most `n` rounds of
  aggregation with the aggregation lets of `Γ`.  It is the closure used by
  the data-flow analysis for aggregation results (non-stable edges).
-/
import Enfflash.DFG

namespace Enfflash

variable {B D : Type}

/-- Values of a term over valuations with values in `U` on its support. -/
def termImg (t : Term D) (U : Set D) : Set D :=
  {d | ∃ w : ℕ → D, (∀ x ∈ t.supp, w x ∈ U) ∧ d = t.eval w}

theorem termImg_finite (t : Term D) (ht : t.WF) (U : Set D) (hU : U.Finite) :
    (termImg t U).Finite := by
  cases t with
  | var x => exact hU.subset (by rintro d ⟨w, hw, rfl⟩; exact hw x (by simp [Term.supp]))
  | const c => exact (Set.finite_singleton c).subset (by rintro d ⟨w, -, rfl⟩; simp)
  | fn f xs =>
    exact (fnImg_finite _ ht U hU).subset (by rintro d ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩)

/-- Rows of the terms `ts` over valuations with values in `U`. -/
def rowsOver (ts : List (Term D)) (U : Set D) : Set (List D) :=
  {r | ∃ w : ℕ → D, (∀ t ∈ ts, ∀ x ∈ t.supp, w x ∈ U) ∧ r = ts.map (Term.eval w)}

theorem rowsOver_finite (ts : List (Term D)) (hts : ∀ t ∈ ts, t.WF) (U : Set D)
    (hU : U.Finite) : (rowsOver ts U).Finite := by
  have hV : (⋃ t ∈ {t | t ∈ ts}, termImg t U).Finite :=
    Set.Finite.biUnion (List.finite_toSet ts) fun t ht => termImg_finite t (hts t ht) U hU
  refine (finite_lists _ hV ts.length).subset ?_
  rintro r ⟨w, hw, rfl⟩
  refine ⟨by simp, fun d hd => ?_⟩
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hd
  exact Set.mem_biUnion ht ⟨w, hw t ht, rfl⟩

theorem rowsOver_mono {ts : List (Term D)} {U U' : Set D} (h : U ⊆ U') :
    rowsOver ts U ⊆ rowsOver ts U' := by
  rintro r ⟨w, hw, rfl⟩; exact ⟨w, fun t ht x hx => h (hw t ht x hx), rfl⟩

/-- Lists of length `k` over `U`. -/
def listsOver (k : ℕ) (U : Set D) : Set (List D) := {ds | ds.length = k ∧ ∀ d ∈ ds, d ∈ U}

/-- Multisets of rows over `R` with multiplicities at most `N`. -/
def boundedMS (R : Set (List D)) (N : ℕ∞) : Set (List D → ℕ∞) :=
  {M | (∀ r, M r ≠ 0 → r ∈ R) ∧ ∀ r, M r ≤ N}

theorem boundedMS_finite (R : Set (List D)) (hR : R.Finite) (n : ℕ) :
    (boundedMS R n).Finite := by
  haveI : Finite R := hR.to_subtype
  have hI : ∀ _ : R, (Set.Iic (n : ℕ∞)).Finite := fun _ => by
    refine ((Set.finite_le_nat n).image (fun m : ℕ => (m : ℕ∞))).subset ?_
    intro x hx
    obtain ⟨m, rfl, hm⟩ := ENat.le_coe_iff.1 hx
    exact ⟨m, hm, rfl⟩
  have hpi : (Set.pi Set.univ fun _ : R => Set.Iic (n : ℕ∞)).Finite := Set.Finite.pi hI
  refine Set.Finite.of_finite_image (f := fun M (r : R) => M r) (hpi.subset ?_) ?_
  · rintro _ ⟨M, hM, rfl⟩ r -; exact hM.2 r
  · intro M hM M' hM' h
    funext r
    by_cases hr : r ∈ R
    · exact congrFun h ⟨r, hr⟩
    · have h1 : M r = 0 := by by_contra h0; exact hr (hM.1 r h0)
      have h2 : M' r = 0 := by by_contra h0; exact hr (hM'.1 r h0)
      rw [h1, h2]

/-- The values in the results of an aggregation `ω` with `k` aggregated
    variables and rows `ts`, over valuations with values in `U`. -/
def aggImg (k : ℕ) (ω : AggOp D) (ts : List (Term D)) (U : Set D) : Set D :=
  {c | ∃ M, M ∈ boundedMS (rowsOver ts U) (listsOver k U).encard ∧ ∃ r, ω.op M r ∧ c ∈ r}

theorem aggImg_finite (k : ℕ) (ω : AggOp D) (ts : List (Term D)) (hts : ∀ t ∈ ts, t.WF)
    (U : Set D) (hU : U.Finite) : (aggImg k ω ts U).Finite := by
  have hL : (listsOver k U).Finite := finite_lists U hU k
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (listsOver k U).encard = n := ⟨_, hL.cast_ncard_eq.symm⟩
  have hMs := boundedMS_finite _ (rowsOver_finite ts hts U hU) n
  refine (hMs.biUnion (t := fun M => ⋃ r ∈ {r | ω.op M r}, {c | c ∈ r}) fun M hM => ?_).subset ?_
  · refine (ω.fin M ((rowsOver_finite ts hts U hU).subset fun r hr => hM.1 r hr)
      fun r => ne_top_of_le_ne_top (ENat.coe_ne_top n) (hM.2 r)).biUnion
      fun r _ => List.finite_toSet r
  · rintro c ⟨M, hM, r, hr, hc⟩
    rw [hn] at hM
    exact Set.mem_biUnion hM (Set.mem_biUnion hr hc)

theorem aggImg_mono {k : ℕ} {ω : AggOp D} {ts : List (Term D)} {U U' : Set D} (h : U ⊆ U') :
    aggImg k ω ts U ⊆ aggImg k ω ts U' := by
  rintro c ⟨M, ⟨hR, hN⟩, r, hr, hc⟩
  refine ⟨M, ⟨fun r hr => rowsOver_mono h (hR r hr), fun r => (hN r).trans ?_⟩, r, hr, hc⟩
  exact Set.encard_le_encard fun ds hds => ⟨hds.1, fun d hd => h (hds.2 d hd)⟩

/-! ## Aggregation closure of a list of lets -/

/-- The terms of the aggregation lets are well-formed. -/
def AggWF (Γ : List (LetDef B ℕ D)) : Prop :=
  ∀ d ∈ Γ, ∀ k ω ts ys φ, d.body = .agg k ω ts ys φ → ∀ t ∈ ts, t.WF

/-- The values computed by an aggregation let from values in `U`. -/
def aggImgOf (d : LetDef B ℕ D) (U : Set D) : Set D :=
  match d.body with
  | .agg k ω ts _ _ => aggImg k ω ts U
  | _ => ∅

/-- One round of aggregation with the lets of `Γ`. -/
def aggStep (Γ : List (LetDef B ℕ D)) (U : Set D) : Set D :=
  U ∪ ⋃ d ∈ {d | d ∈ Γ}, aggImgOf d U

/-- At most `n` rounds of aggregation. -/
def aggClo (Γ : List (LetDef B ℕ D)) (n : ℕ) : Set D → Set D := (aggStep Γ)^[n]

section
variable {Γ : List (LetDef B ℕ D)}

theorem aggStep_mono {U U' : Set D} (h : U ⊆ U') : aggStep Γ U ⊆ aggStep Γ U' := by
  rintro c (hc | hc)
  · exact Or.inl (h hc)
  · obtain ⟨d, hd, hc⟩ := Set.mem_iUnion₂.1 hc
    refine Or.inr (Set.mem_iUnion₂.2 ⟨d, hd, ?_⟩)
    unfold aggImgOf at hc ⊢
    split at hc
    · exact aggImg_mono h hc
    · exact hc

theorem aggStep_finite (hwf : AggWF Γ) {U : Set D} (hU : U.Finite) : (aggStep Γ U).Finite := by
  refine hU.union (Set.Finite.biUnion (List.finite_toSet Γ) fun d hd => ?_)
  unfold aggImgOf
  split
  · rename_i k ω ts _ _ hb
    exact aggImg_finite k ω ts (hwf d hd _ _ _ _ _ hb) U hU
  · exact Set.finite_empty

theorem aggClo_ext (n : ℕ) (U : Set D) : U ⊆ aggClo Γ n U := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [aggClo, Function.iterate_succ_apply']
    exact ih.trans Set.subset_union_left

theorem aggClo_mono (n : ℕ) {U U' : Set D} (h : U ⊆ U') : aggClo Γ n U ⊆ aggClo Γ n U' := by
  induction n with
  | zero => exact h
  | succ n ih => simp only [aggClo, Function.iterate_succ_apply']; exact aggStep_mono ih

theorem aggClo_le {m n : ℕ} (h : m ≤ n) (U : Set D) : aggClo Γ m U ⊆ aggClo Γ n U := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
    refine ih.trans ?_
    simp only [aggClo, Function.iterate_succ_apply']
    exact Set.subset_union_left

theorem aggClo_finite (hwf : AggWF Γ) (n : ℕ) {U : Set D} (hU : U.Finite) :
    (aggClo Γ n U).Finite := by
  induction n with
  | zero => exact hU
  | succ n ih => simp only [aggClo, Function.iterate_succ_apply']; exact aggStep_finite hwf ih

/-- An aggregation let of `Γ` applied to `aggClo n U` stays in `aggClo (n+1) U`. -/
theorem aggImg_clo {d : LetDef B ℕ D} (hd : d ∈ Γ) {k : ℕ} {ω : AggOp D} {ts : List (Term D)}
    {ys : List ℕ} {φ : Fm B ℕ D} (hb : d.body = .agg k ω ts ys φ) (n : ℕ) (U : Set D) :
    aggImg k ω ts (aggClo Γ n U) ⊆ aggClo Γ (n + 1) U := by
  intro c hc
  simp only [aggClo, Function.iterate_succ_apply']
  refine Or.inr (Set.mem_iUnion₂.2 ⟨d, hd, ?_⟩)
  unfold aggImgOf; rw [hb]; exact hc

end

end Enfflash
