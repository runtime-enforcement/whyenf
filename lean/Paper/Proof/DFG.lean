/-
  The DFG of `R` as a finite graph with levels.
-/
import Paper.Proof.GNames

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem atoms_finite : ∀ φ : Formula Voc, φ.atoms.Finite
  | .top | .eq .. => Set.finite_empty
  | .pred e ts => Set.finite_singleton _
  | .neg φ | .ex _ φ | .next _ φ | .prev _ φ | .eventually _ φ | .agg _ _ _ _ φ => atoms_finite φ
  | .and φ ψ | .since _ φ ψ | .letin _ _ φ ψ => (atoms_finite φ).union (atoms_finite ψ)

theorem trigAtoms_finite (c : EClause Voc) : c.trigAtoms.Finite := by
  refine Set.Finite.union ?_ (atoms_finite _)
  refine (Set.Finite.biUnion (s := {κ | κ ∈ c.π}) (List.finite_toSet _)
    (t := fun κ => {a : Voc.ℰ × List (Term Voc) | GAtom.pred a.1 a.2 ∈ κ}) fun κ _ => ?_).subset ?_
  · refine (List.finite_toSet κ).preimage (f := fun a : Voc.ℰ × List (Term Voc) => GAtom.pred a.1 a.2) ?_
    rintro ⟨a1, a2⟩ - ⟨b1, b2⟩ - h
    simp only [GAtom.pred.injEq] at h; rw [h.1, h.2]
  · rintro a ⟨κ, hκ, ha⟩; exact Set.mem_biUnion hκ ha

/-- The positions of a list of atoms. -/
def posOf (A : Set (Voc.ℰ × List (Term Voc))) : Set (Pos Voc) :=
  {q | ∃ a ∈ A, q.1 = a.1 ∧ q.2 < a.2.length}

theorem posOf_finite {A : Set (Voc.ℰ × List (Term Voc))} (h : A.Finite) : (posOf A).Finite := by
  refine (h.biUnion fun a _ => ((Set.finite_lt_nat a.2.length).image fun i => (a.1, i))).subset ?_
  rintro ⟨e, i⟩ ⟨a, ha, he, hi⟩
  exact Set.mem_biUnion ha ⟨i, hi, by simp only at he; rw [he]⟩

namespace Setup
variable (U : Setup Voc)

theorem R_finite : U.R.Finite := (List.finite_toSet U.rs).subset fun c hc => (U.hrs c).2 hc

/-- All atoms. -/
def AllAtoms : Set (Voc.ℰ × List (Term Voc)) :=
  (⋃ c ∈ U.R, c.trigAtoms) ∪ (⋃ c ∈ U.R, {(c.ε.name, c.ε.args)}) ∪
    (⋃ d ∈ {d | d ∈ U.L.lets}, d.φ.atoms) ∪
    (⋃ d ∈ {d | d ∈ U.L.lets}, {(d.e, d.xs.map Term.var)})

theorem AllAtoms_finite : U.AllAtoms.Finite :=
  (((U.R_finite.biUnion fun c _ => trigAtoms_finite c).union
    (U.R_finite.biUnion fun _ _ => Set.finite_singleton _)).union
    ((List.finite_toSet _).biUnion fun d _ => atoms_finite _)).union
    ((List.finite_toSet _).biUnion fun _ _ => Set.finite_singleton _)

theorem dfg_finite : Graph.FiniteGraph (DFG U.L.lets U.R) := by
  refine ⟨posOf U.AllAtoms, posOf_finite U.AllAtoms_finite, fun q q' h => ?_⟩
  rcases h with ⟨c, t, hc, x, ⟨ts, hts, hk⟩, hq', ht, -⟩ | ⟨d, hd, hq', y, hy, ts, hts, z, hz, -⟩
  · refine ⟨⟨(q.1, ts), Or.inl (Or.inl (Or.inl (Set.mem_biUnion hc hts))), rfl, ?_⟩,
      ⟨(c.ε.name, c.ε.args), Or.inl (Or.inl (Or.inr (Set.mem_biUnion hc rfl))), hq', ?_⟩⟩
    · exact (List.getElem?_eq_some_iff.1 hk).1
    · exact (List.getElem?_eq_some_iff.1 ht).1
  · refine ⟨⟨(q.1, ts), Or.inl (Or.inr (Set.mem_biUnion (s := {d | d ∈ U.L.lets}) hd hts)), rfl, ?_⟩,
      ⟨(d.e, d.xs.map Term.var), Or.inr (Set.mem_biUnion (s := {d | d ∈ U.L.lets}) hd rfl), hq', ?_⟩⟩
    · exact (List.getElem?_eq_some_iff.1 hz).1
    · simpa using (List.getElem?_eq_some_iff.1 hy).1

/-- The strict (non-stable) edges. -/
def NS (q q' : Pos Voc) : Prop :=
  (∃ c t, DFGEdge U.R c t q q' ∧ ¬ StableEdge U.O U.L.lets t q q') ∨
    (LetEdge U.L.lets q q' ∧ (AggResult U.L.lets q ∨ AggResult U.L.lets q'))

theorem NS_sub : ∀ q q', U.NS q q' → DFG U.L.lets U.R q q' := by
  rintro q q' (⟨c, t, h, -⟩ | ⟨h, -⟩)
  · exact Or.inl ⟨c, t, h⟩
  · exact Or.inr h

theorem NS_acyc : ∀ q q', U.NS q q' → ¬ Relation.ReflTransGen (DFG U.L.lets U.R) q' q := by
  rintro q q' (⟨c, t, h, hn⟩ | ⟨h, ha⟩)
  · exact U.dfg.1 c t q q' h hn
  · exact U.dfg.2 q q' h ha

/-- The level of a position. -/
noncomputable def Lv (q : Pos Voc) : ℕ := Graph.level (DFG U.L.lets U.R) U.NS q

theorem Lv_mono {q q' : Pos Voc} (h : DFG U.L.lets U.R q q') : U.Lv q ≤ U.Lv q' :=
  Graph.level_mono U.dfg_finite U.NS_sub h

theorem Lv_strict {q q' : Pos Voc} (h : U.NS q q') : U.Lv q < U.Lv q' :=
  Graph.level_strict U.dfg_finite U.NS_sub U.NS_acyc h

/-- The maximal level. -/
noncomputable def Lmax : ℕ := {p : Pos Voc × Pos Voc | U.NS p.1 p.2}.ncard

theorem Lv_le (q : Pos Voc) : U.Lv q ≤ U.Lmax :=
  Set.ncard_le_ncard (fun _ hp => hp.1) (Graph.strict_finite U.dfg_finite U.NS_sub)

end Setup

end Paper
