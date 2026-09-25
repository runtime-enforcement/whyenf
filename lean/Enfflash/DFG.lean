/-
  Enfflash formalization — the data-flow termination criterion (paper,
  Section 4.5, "Termination", Figure 8).

  The Data-Flow Graph of a section has the argument positions `e.i` as nodes
  and an edge `e.i → e'.j` whenever a rule acting on `e'` reads, in its `j`-th
  effect argument, a variable bound at position `e.i` of its trigger (lets
  being decomposed into the positions their arguments come from).  The edge
  is *stable* if the argument is a variable, a constant, or an application of
  stable functions, and *non-stable* otherwise (it may create new values).
  Stable functions are given by a *stability closure* `Stab` (`StabOp`):
  applying stable functions to a finite set of values, any number of times,
  only yields finitely many values (e.g. comparisons, negation; the
  compiler's `sfun`/strict functions).

  `dfg_terminates`: if no non-stable edge lies on a cycle of the DFG, the
  section reaches its fixpoint after finitely many passes.

  Proof idea: the *level* of a position (the number of non-stable edges
  upstream of it, `Graph.level`) is monotone along edges and strictly
  increases along non-stable edges.  Values at a position of level `k` lie in a
  finite set `Vlev k`, obtained from the initial values by `k` rounds of
  function application, each closed under `Stab`.  Hence all actions lie in a
  finite universe.
-/
import Enfflash.Dataflow
import Enfflash.Graph

set_option autoImplicit false

namespace Enfflash

universe u
variable {B L D : Type u}

/-- Argument positions `e.i`. -/
abbrev Pos (B L : Type u) := Ev B L × ℕ

/-- Values occurring at position `q` in `W`. -/
def valsAt (W : DB B L D) (q : Pos B L) : Set D :=
  {d | ∃ as, (q.1, as) ∈ W ∧ as[q.2]? = some d}

/-- A monotone, extensive, finiteness-preserving operator on value sets (the
    values computed by aggregations, `aggClo`). -/
structure CloOp (A : Set D → Set D) : Prop where
  ext : ∀ U, U ⊆ A U
  mono : ∀ U U', U ⊆ U' → A U ⊆ A U'
  finite : ∀ U, U.Finite → (A U).Finite

/-- Data flow through lets: the `i`-th argument of a tuple of an enumerable
    let `p` (`ok p`) is a known value, comes from one of the positions
    `lsrc p i` (stable), or is computed by aggregation (`A`) from known values
    and the values at the positions `nsrc p i` (non-stable). -/
def LetsFlow (K : Ctx B L D) (V : Set D) (lsrc nsrc : L → ℕ → List (Pos B L))
    (A : Set D → Set D) (ok : L → Prop) : Prop :=
  ∀ W p as, ok p → K.lv W p as → ∀ i d, as[i]? = some d →
    d ∈ V ∨ (∃ q ∈ lsrc p i, d ∈ valsAt W q) ∨
      d ∈ A (V ∪ {d' | ∃ q ∈ nsrc p i, d' ∈ valsAt W q})

section
variable (lsrc nsrc : L → ℕ → List (Pos B L))

/-- `q` is a (stable) source of variable `x` in guard atom `a`. -/
def GAtom.src (x : ℕ) : GAtom B L D → Pos B L → Prop
  | .pred (.ev e) ts, q => q.1 = e ∧ ts[q.2]? = some (.var x)
  | .pred (.lp p) ts, q => ∃ i, ts[i]? = some (.var x) ∧ q ∈ lsrc p i
  | .eq _ _, _ => False

/-- `q` is a non-stable source of variable `x` in guard atom `a` (through an
    aggregation). -/
def GAtom.asrc (x : ℕ) : GAtom B L D → Pos B L → Prop
  | .pred (.lp p) ts, q => ∃ i, ts[i]? = some (.var x) ∧ q ∈ nsrc p i
  | _, _ => False

/-- All positions read by a guard atom. -/
def GAtom.positions : GAtom B L D → Set (Pos B L)
  | .pred (.ev e) ts => {q | q.1 = e ∧ q.2 < ts.length}
  | .pred (.lp p) ts => ⋃ i ∈ {i | i < ts.length}, {q | q ∈ lsrc p i ∨ q ∈ nsrc p i}
  | .eq _ _ => ∅

def Clause.src (c : Clause B L D) (x : ℕ) (q : Pos B L) : Prop :=
  ∃ κ ∈ c.trig.guards, ∃ a ∈ κ, a.src lsrc x q

def Clause.asrc (c : Clause B L D) (x : ℕ) (q : Pos B L) : Prop :=
  ∃ κ ∈ c.trig.guards, ∃ a ∈ κ, a.asrc nsrc x q

end

/-- A *stability closure*: the values obtained from a finite set by applying
    stable functions any number of times form a finite set. -/
structure StabOp (Stab : Set D → Set D) : Prop where
  ext : ∀ U, U ⊆ Stab U
  mono : ∀ U U', U ⊆ U' → Stab U ⊆ Stab U'
  idem : ∀ U, Stab (Stab U) ⊆ Stab U
  finite : ∀ U, U.Finite → (Stab U).Finite

/-- A term is stable (w.r.t. `Stab`) if it is a variable, a constant, or an
    application of stable functions: its value lies in the stability closure
    of the values of its variables. -/
def Term.stableIn (Stab : Set D → Set D) : Term D → Prop
  | .fn f xs => ∀ v, f v ∈ Stab {d | ∃ x ∈ xs, v x = d}
  | _ => True

section
variable (lsrc nsrc : L → ℕ → List (Pos B L))

/-- DFG edges of a list of rules. -/
def DFE (rules : List (Clause B L D)) (q q' : Pos B L) : Prop :=
  ∃ c ∈ rules, ∃ j t, c.eff.args[j]? = some t ∧ q' = (c.eff.name, j) ∧
    ∃ x ∈ t.supp, x < c.nloc ∧ (c.src lsrc x q ∨ c.asrc nsrc x q)

/-- Non-stable DFG edges: through a term that is not stable, or through an
    aggregation. -/
def DFS (Stab : Set D → Set D) (rules : List (Clause B L D)) (q q' : Pos B L) : Prop :=
  ∃ c ∈ rules, ∃ j t, c.eff.args[j]? = some t ∧ q' = (c.eff.name, j) ∧
    ∃ x ∈ t.supp, x < c.nloc ∧ ((¬ t.stableIn Stab ∧ c.src lsrc x q) ∨ c.asrc nsrc x q)

/-- The paper's criterion: no non-stable edge lies on a cycle. -/
def DFGAcyclic (Stab : Set D → Set D) (rules : List (Clause B L D)) : Prop :=
  ∀ q q', DFS lsrc nsrc Stab rules q q' → ¬ Relation.ReflTransGen (DFE lsrc nsrc rules) q' q

end

/-- Well-formed rules for the data-flow analysis: function terms only read
    their support, constants are known, local variables read by effects are
    bound by every guard, and context variables have known values. -/
structure DFClause (V : Set D) (v₀ : ℕ → D) (ok : L → Prop) (c : Clause B L D) : Prop where
  wf : ∀ t ∈ c.eff.args, t.WF
  consts : ∀ t ∈ c.eff.args, ∀ d, t = .const d → d ∈ V
  locals : ∀ t ∈ c.eff.args, ∀ x ∈ t.supp, x < c.nloc → c.trig.guards.bindsAll x
  ctx : ∀ t ∈ c.eff.args, ∀ x ∈ t.supp, c.nloc ≤ x → v₀ (x - c.nloc) ∈ V
  eqs : ∀ κ ∈ c.trig.guards, ∀ a ∈ κ, ∀ t d, a = .eq t d → d ∈ V
  lets : ∀ κ ∈ c.trig.guards, ∀ a ∈ κ, ∀ q ts, a = .pred (.lp q) ts → ok q

section
variable {lsrc nsrc : L → ℕ → List (Pos B L)}

theorem DFS.dfe {Stab : Set D → Set D} {rules : List (Clause B L D)} {q q'}
    (h : DFS lsrc nsrc Stab rules q q') : DFE lsrc nsrc rules q q' := by
  obtain ⟨c, hc, j, t, h1, h2, x, hx, hxl, h | h⟩ := h
  · exact ⟨c, hc, j, t, h1, h2, x, hx, hxl, Or.inl h.2⟩
  · exact ⟨c, hc, j, t, h1, h2, x, hx, hxl, Or.inr h⟩

theorem positions_finite (a : GAtom B L D) : (a.positions lsrc nsrc).Finite := by
  rcases a with ⟨p, ts⟩ | ⟨t, d⟩
  · cases p with
    | ev e =>
      refine ((Set.finite_singleton e).prod (Set.finite_lt_nat ts.length)).subset ?_
      rintro ⟨e', i⟩ ⟨h1, h2⟩; exact ⟨h1, h2⟩
    | lp p =>
      exact Set.Finite.biUnion (Set.finite_lt_nat _) fun i _ =>
        ((List.finite_toSet (lsrc p i)).union (List.finite_toSet (nsrc p i))).subset
          fun q hq => hq
  · exact Set.finite_empty

theorem src_positions {x : ℕ} {a : GAtom B L D} {q : Pos B L}
    (h : a.src lsrc x q ∨ a.asrc nsrc x q) : q ∈ a.positions lsrc nsrc := by
  rcases a with ⟨p, ts⟩ | ⟨t, d⟩
  · cases p with
    | ev e =>
      rcases h with ⟨h1, h2⟩ | h
      · exact ⟨h1, (List.getElem?_eq_some_iff.1 h2).1⟩
      · exact h.elim
    | lp p =>
      rcases h with ⟨i, hi, hq⟩ | ⟨i, hi, hq⟩
      · exact Set.mem_biUnion (x := i) (List.getElem?_eq_some_iff.1 hi).1 (Or.inl hq)
      · exact Set.mem_biUnion (x := i) (List.getElem?_eq_some_iff.1 hi).1 (Or.inr hq)
  · rcases h with h | h <;> exact h.elim

variable (lsrc nsrc) in
theorem DFE.finite (rules : List (Clause B L D)) :
    Graph.FiniteGraph (DFE lsrc nsrc rules) := by
  refine ⟨⋃ c ∈ rules, ((⋃ κ ∈ c.trig.guards, ⋃ a ∈ κ, a.positions lsrc nsrc) ∪
      {q | q.1 = c.eff.name ∧ q.2 < c.eff.args.length}),
    Set.Finite.biUnion (List.finite_toSet rules) fun c _ =>
      (Set.Finite.biUnion (List.finite_toSet _) fun κ _ =>
        Set.Finite.biUnion (List.finite_toSet _) fun a _ => positions_finite a).union
      (((Set.finite_singleton c.eff.name).prod (Set.finite_lt_nat _)).subset
        fun q hq => ⟨hq.1, hq.2⟩), ?_⟩
  rintro q q' ⟨c, hc, j, t, ht, rfl, x, -, -, hs⟩
  have hpos : ∃ κ ∈ c.trig.guards, ∃ a ∈ κ, a.src lsrc x q ∨ a.asrc nsrc x q := by
    rcases hs with ⟨κ, hκ, a, ha, h⟩ | ⟨κ, hκ, a, ha, h⟩
    exacts [⟨κ, hκ, a, ha, Or.inl h⟩, ⟨κ, hκ, a, ha, Or.inr h⟩]
  obtain ⟨κ, hκ, a, ha, hsrc⟩ := hpos
  refine ⟨Set.mem_biUnion hc (Or.inl (Set.mem_biUnion hκ (Set.mem_biUnion ha
    (src_positions hsrc)))), Set.mem_biUnion hc (Or.inr ⟨rfl, ?_⟩)⟩
  exact (List.getElem?_eq_some_iff.1 ht).1

/-! ### Values of guarded variables -/

theorem guarded_value {K : Ctx B L D} {V : Set D} {A : Set D → Set D} (hA : CloOp A)
    {ok : L → Prop} (hK : LetsFlow K V lsrc nsrc A ok) {W : DB B L D} {c : Clause B L D}
    (hc : DFClause V K.v₀ ok c)
    {w : ℕ → D} (htr : c.trig.sat (ptTr W (K.lv W)) 0 w) {x : ℕ}
    (hb : c.trig.guards.bindsAll x) :
    w x ∈ V ∨ (∃ q, c.src lsrc x q ∧ w x ∈ valsAt W q) ∨
      w x ∈ A (V ∪ {d | ∃ q, c.asrc nsrc x q ∧ d ∈ valsAt W q}) := by
  obtain ⟨κ, hκ, hall⟩ := htr.1
  obtain ⟨a, ha, hbind⟩ := hb κ hκ
  have hsat := hall a ha
  rcases a with ⟨p, ts⟩ | ⟨t, d⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hbind
    have hval : (ts.map (Term.eval w))[i]? = some (w x) := by
      rw [List.getElem?_map, hi]; rfl
    cases p with
    | ev e => exact Or.inr (Or.inl ⟨(e, i), ⟨κ, hκ, _, ha, rfl, hi⟩, _, hsat, hval⟩)
    | lp p =>
      rcases hK W p _ (hc.lets κ hκ _ ha p ts rfl) hsat i _ hval with h | ⟨q, hq, hv⟩ | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨q, ⟨κ, hκ, _, ha, i, hi, hq⟩, hv⟩)
      · refine Or.inr (Or.inr (hA.mono _ _ ?_ h))
        rintro d (hd | ⟨q, hq, hv⟩)
        · exact Or.inl hd
        · exact Or.inr ⟨q, ⟨κ, hκ, _, ha, i, hi, hq⟩, hv⟩
  · simp only [GAtom.binds] at hbind
    subst hbind
    exact Or.inl (by
      have := hc.eqs κ hκ _ ha _ _ rfl
      simp only [GAtom.sat, Term.eval] at hsat; rwa [hsat])

end

/-! ### Finitely many values per level -/

/-- Values created by applying a function term to values in `U`. -/
def fnImg (t : Term D) (U : Set D) : Set D :=
  match t with
  | .fn f xs => {d | ∃ w : ℕ → D, (∀ n ∈ xs, w n ∈ U) ∧ d = f w}
  | _ => ∅

theorem fnImg_mono (t : Term D) {U U' : Set D} (h : U ⊆ U') : fnImg t U ⊆ fnImg t U' := by
  cases t with
  | fn f xs => rintro d ⟨w, hw, rfl⟩; exact ⟨w, fun n hn => h (hw n hn), rfl⟩
  | _ => exact fun _ hd => hd

theorem fnImg_finite (t : Term D) (ht : t.WF) (U : Set D) (hU : U.Finite) :
    (fnImg t U).Finite := by
  cases t with
  | var => exact Set.finite_empty
  | const => exact Set.finite_empty
  | fn f xs =>
    by_cases hD : Nonempty D
    · obtain ⟨d₀⟩ := hD
      let mk : List D → ℕ → D := fun ls n => ls.getD (xs.idxOf n) d₀
      refine ((finite_lists U hU xs.length).image (fun ls => f (mk ls))).subset ?_
      rintro d ⟨w, hw, rfl⟩
      refine ⟨xs.map w, ⟨by simp, fun e he => ?_⟩, ht _ _ fun n hn => ?_⟩
      · obtain ⟨n, hn, rfl⟩ := List.mem_map.1 he; exact hw n hn
      · have hlt := List.idxOf_lt_length_of_mem hn
        show (xs.map w).getD _ d₀ = w n
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt]
        simp [List.getElem_idxOf hlt]
    · refine Set.finite_empty.subset ?_
      rintro d ⟨w, -, -⟩; exact hD ⟨w 0⟩

section
variable (sec : List (Clause B L D))

/-- New values from one round of function application. -/
def Fimg (U : Set D) : Set D := {d | ∃ c ∈ sec, ∃ t ∈ c.eff.args, d ∈ fnImg t U}

/-- Values available at level `k`: `k` rounds of aggregation (`A`) and
    function application, each closed under the stable functions. -/
def Vlev (Stab A : Set D → Set D) (Vb : Set D) : ℕ → Set D
  | 0 => Stab (A Vb ∪ Fimg sec (A Vb))
  | k + 1 => Stab (A (Vlev Stab A Vb k) ∪ Fimg sec (A (Vlev Stab A Vb k)))

/-- Values available strictly below level `k` (after aggregation). -/
def lowVals (Stab A : Set D → Set D) (Vb : Set D) : ℕ → Set D
  | 0 => A Vb
  | k + 1 => A (Vlev sec Stab A Vb k)

end

section
variable (sec : List (Clause B L D)) {Stab A : Set D → Set D} (hS : StabOp Stab) (hA : CloOp A)
  (Vb : Set D)
include hS hA

omit hS hA in
theorem Vlev_eq (k : ℕ) :
    Vlev sec Stab A Vb k = Stab (lowVals sec Stab A Vb k ∪ Fimg sec (lowVals sec Stab A Vb k)) := by
  cases k <;> rfl

omit hA in
theorem low_Vlev (k : ℕ) : lowVals sec Stab A Vb k ⊆ Vlev sec Stab A Vb k := by
  rw [Vlev_eq sec]; exact Set.subset_union_left.trans (hS.ext _)

omit hA in
theorem Fimg_low (k : ℕ) : Fimg sec (lowVals sec Stab A Vb k) ⊆ Vlev sec Stab A Vb k := by
  rw [Vlev_eq sec]; exact Set.subset_union_right.trans (hS.ext _)

theorem Vlev_mono {k m : ℕ} (h : k ≤ m) : Vlev sec Stab A Vb k ⊆ Vlev sec Stab A Vb m := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans ((hA.ext _).trans (low_Vlev sec hS Vb (_ + 1)))

theorem base_low (k : ℕ) : Vb ⊆ lowVals sec Stab A Vb k := by
  cases k with
  | zero => exact hA.ext _
  | succ k =>
    refine (?_ : Vb ⊆ Vlev sec Stab A Vb k).trans (hA.ext _)
    exact ((hA.ext _).trans (low_Vlev sec hS Vb 0)).trans (Vlev_mono sec hS hA Vb (Nat.zero_le k))

theorem base_Vlev (k : ℕ) : Vb ⊆ Vlev sec Stab A Vb k :=
  (base_low sec hS hA Vb k).trans (low_Vlev sec hS Vb k)

theorem lower_low {m k : ℕ} (h : m < k) : Vlev sec Stab A Vb m ⊆ lowVals sec Stab A Vb k := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact (Vlev_mono sec hS hA Vb (by omega)).trans (hA.ext _)

/-- Aggregations over known values and values strictly below level `k`. -/
theorem A_low (k : ℕ) {S : Set D} (hS' : ∀ d ∈ S, ∃ m < k, d ∈ Vlev sec Stab A Vb m) :
    A (Vb ∪ S) ⊆ lowVals sec Stab A Vb k := by
  cases k with
  | zero =>
    refine hA.mono _ _ (Set.union_subset le_rfl fun d hd => ?_)
    obtain ⟨m, hm, -⟩ := hS' d hd; omega
  | succ k =>
    refine hA.mono _ _ (Set.union_subset (base_Vlev sec hS hA Vb k) fun d hd => ?_)
    obtain ⟨m, hm, hd⟩ := hS' d hd
    exact Vlev_mono sec hS hA Vb (by omega) hd

omit hA in
theorem Vlev_closed (k : ℕ) : Stab (Vlev sec Stab A Vb k) ⊆ Vlev sec Stab A Vb k := by
  cases k <;> exact hS.idem _

theorem Vlev_finite (hwf : ∀ c ∈ sec, ∀ t ∈ c.eff.args, t.WF)
    (hVb : Vb.Finite) : ∀ k, (Vlev sec Stab A Vb k).Finite := by
  have hF : ∀ U : Set D, U.Finite → (Fimg sec U).Finite := by
    intro U hU
    have : Fimg sec U = ⋃ c ∈ {c | c ∈ sec}, ⋃ t ∈ {t | t ∈ c.eff.args}, fnImg t U := by
      ext d; simp [Fimg]
    rw [this]
    exact Set.Finite.biUnion (List.finite_toSet sec) fun c hc =>
      Set.Finite.biUnion (List.finite_toSet _) fun t ht => fnImg_finite t (hwf c hc t ht) U hU
  intro k
  induction k with
  | zero => exact hS.finite _ ((hA.finite _ hVb).union (hF _ (hA.finite _ hVb)))
  | succ k ih => exact hS.finite _ ((hA.finite _ ih).union (hF _ (hA.finite _ ih)))

end

/-! ### Termination -/

/-- **Termination (data-flow criterion).**  If no non-stable edge of the
    section's data-flow graph lies on a cycle, the section reaches its fixpoint
    after finitely many passes, from any finite input and initial actions. -/
theorem dfg_terminates (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D))
    {Stab : Set D → Set D} (hS : StabOp Stab) {A : Set D → Set D} (hA : CloOp A)
    (V : Set D) (hV : V.Finite) (hD : D₀.Finite) (lsrc nsrc : L → ℕ → List (Pos B L))
    (ok : L → Prop) (hK : LetsFlow K V lsrc nsrc A ok) (hc : ∀ c ∈ sec, DFClause V K.v₀ ok c)
    (hacyc : DFGAcyclic lsrc nsrc Stab sec) (X₀ : Set (Act B L D)) (hX₀ : X₀.Finite) :
    ∃ n, Fixed K D₀ sec ((step K D₀ sec)^[n] X₀) ∧ ((step K D₀ sec)^[n] X₀).Finite := by
  classical
  -- levels of positions
  have hG := DFE.finite lsrc nsrc sec
  have hSE : ∀ q q', DFS lsrc nsrc Stab sec q q' → DFE lsrc nsrc sec q q' := fun _ _ h => h.dfe
  let lvl := Graph.level (DFE lsrc nsrc sec) (DFS lsrc nsrc Stab sec)
  let M := {p : Pos B L × Pos B L | DFS lsrc nsrc Stab sec p.1 p.2}.ncard
  have hlvl : ∀ q, lvl q ≤ M := Graph.level_le hG hSE
  -- values
  let Vb := V ∪ adom D₀ ∪ actDom X₀
  have hadom : (adom D₀).Finite := by
    have : adom D₀ = ⋃ x ∈ D₀, {d | d ∈ x.2} := by ext d; simp [adom]
    rw [this]; exact hD.biUnion fun x _ => List.finite_toSet x.2
  have hact : (actDom X₀).Finite := by
    have : actDom X₀ = ⋃ a ∈ X₀, {d | d ∈ a.args} := by ext d; simp [actDom]
    rw [this]; exact hX₀.biUnion fun a _ => List.finite_toSet a.args
  have hVb : Vb.Finite := (hV.union hadom).union hact
  let Vl := Vlev sec Stab A Vb
  have hVl : ∀ k, (Vl k).Finite := Vlev_finite sec hS hA Vb (fun c h => (hc c h).wf) hVb
  -- well-leveled actions
  let Good : Set (Act B L D) :=
    {a | ∀ j d, a.args[j]? = some d → d ∈ Vl (lvl (a.name, j))}
  let U : Set (Act B L D) := X₀ ∪ ({a | ∃ c ∈ sec, a.name = c.eff.name ∧
    a.args.length = c.eff.args.length ∧ ∃ as, a = c.eff.withArgs as} ∩ Good)
  have hX₀good : X₀ ⊆ Good := fun a ha j d hd =>
    base_Vlev sec hS hA Vb _ (Or.inr ⟨a, ha, List.mem_of_getElem? hd⟩)
  have hUgood : U ⊆ Good := fun a ha => ha.elim (hX₀good ·) (·.2)
  have hUfin : U.Finite := by
    refine hX₀.union (((Set.Finite.biUnion (List.finite_toSet sec) fun c _ =>
      (finite_lists (Vl M) (hVl M) c.eff.args.length).image (fun as => c.eff.withArgs as))).subset ?_)
    rintro a ⟨⟨c, hc', -, hlen, as, rfl⟩, hgood⟩
    refine Set.mem_biUnion hc' ⟨as, ⟨by simpa [Effect.withArgs_args] using hlen, fun d hd => ?_⟩, rfl⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hd
    exact Vlev_mono sec hS hA Vb (hlvl _) (hgood j d (by rwa [Effect.withArgs_args]))
  -- values in working sets are well-leveled
  have hwork : ∀ Y ⊆ U, ∀ q d, d ∈ valsAt (work D₀ Y) q → d ∈ Vl (lvl q) := by
    rintro Y hY ⟨e, k⟩ d ⟨as, (⟨has, -⟩ | has), hd⟩
    · exact base_Vlev sec hS hA Vb _ (Or.inl (Or.inr ⟨_, has, List.mem_of_getElem? hd⟩))
    · exact hUgood (hY has) k d hd
  -- closure of the universe
  have hclosed : ∀ Y ⊆ U, ∀ c ∈ sec, ∀ a, fires K (work D₀ Y) c a → a ∈ U := by
    intro Y hY c hcs a ha
    obtain ⟨ds, hds, htr, rfl⟩ := ha
    set w := vapp ds K.v₀
    have hC := hc c hcs
    refine Or.inr ⟨⟨c, hcs, Effect.act_name _ _, by
      rw [Effect.act_eq_withArgs, Effect.withArgs_args]; simp, _, Effect.act_eq_withArgs _ _⟩, ?_⟩
    intro j d hd
    rw [Effect.act_name]
    rw [Effect.act_eq_withArgs, Effect.withArgs_args, List.getElem?_map] at hd
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 hd
    have htm : t ∈ c.eff.args := List.mem_of_getElem? ht
    set Lv := lvl (c.eff.name, j)
    -- the value of a variable read by the effect
    have hvar : ∀ x ∈ t.supp, w x ∈ Vb ∨
        (∃ q, DFE lsrc nsrc sec q (c.eff.name, j) ∧
          (¬ t.stableIn Stab → DFS lsrc nsrc Stab sec q (c.eff.name, j)) ∧ w x ∈ Vl (lvl q)) ∨
        w x ∈ lowVals sec Stab A Vb Lv := by
      intro x hx
      by_cases hxl : x < c.nloc
      · rcases guarded_value hA hK hC htr (hC.locals t htm x hx hxl) with h | ⟨q, hq, hv⟩ | h
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inr (Or.inl ⟨q, ⟨c, hcs, j, t, ht, rfl, x, hx, hxl, Or.inl hq⟩,
            fun hns => ⟨c, hcs, j, t, ht, rfl, x, hx, hxl, Or.inl ⟨hns, hq⟩⟩, hwork Y hY q _ hv⟩)
        · have hS' : ∀ d ∈ {d | ∃ q, DFS lsrc nsrc Stab sec q (c.eff.name, j) ∧ d ∈ Vl (lvl q)},
              ∃ m < Lv, d ∈ Vl m := by
            rintro d ⟨q, hq, hd⟩; exact ⟨lvl q, Graph.level_strict hG hSE hacyc hq, hd⟩
          refine Or.inr (Or.inr (A_low sec hS hA Vb Lv hS' (hA.mono _ _ ?_ h)))
          · rintro d (hd | ⟨q, hq, hv⟩)
            · exact Or.inl (Or.inl (Or.inl hd))
            · exact Or.inr ⟨q, ⟨c, hcs, j, t, ht, rfl, x, hx, hxl, Or.inr hq⟩, hwork Y hY q _ hv⟩
      · left; left; left
        have := hC.ctx t htm x hx (by omega)
        obtain ⟨m, rfl⟩ : ∃ m, x = m + c.nloc := ⟨x - c.nloc, by omega⟩
        simp only [w, ← hds, vapp_ge]
        simpa using this
    -- every variable read by the effect has a value at its level
    have hvarL : ∀ x ∈ t.supp, w x ∈ Vl Lv := by
      intro x hx
      rcases hvar x hx with h | ⟨q, hq, -, hv⟩ | h
      · exact base_Vlev sec hS hA Vb _ h
      · exact Vlev_mono sec hS hA Vb (Graph.level_mono hG hSE hq) hv
      · exact low_Vlev sec hS Vb _ h
    show t.eval w ∈ Vl Lv
    cases t with
    | const d => exact base_Vlev sec hS hA Vb _ (Or.inl (Or.inl (hC.consts _ htm d rfl)))
    | var x => exact hvarL x (by simp [Term.supp])
    | fn f xs =>
      show f w ∈ Vl Lv
      by_cases hst : (Term.fn f xs).stableIn Stab
      · -- a stable term: its value is in the closure of its arguments
        refine Vlev_closed sec hS Vb _ (hS.mono _ _ ?_ (hst w))
        rintro _ ⟨n, hn, rfl⟩
        exact hvarL n hn
      · -- a non-stable term: one more round of function application
        refine Fimg_low sec hS Vb Lv ⟨c, hcs, _, htm, w, fun n hn => ?_, rfl⟩
        rcases hvar n hn with h | ⟨q, -, hq, hv⟩ | h
        · exact base_low sec hS hA Vb _ h
        · exact lower_low sec hS hA Vb (Graph.level_strict hG hSE hacyc (hq hst)) hv
        · exact h
  obtain ⟨n, -, hn, hsub⟩ := fixpoint_exists K D₀ sec U hUfin X₀ Set.subset_union_left hclosed
  exact ⟨n, hn, hUfin.subset hsub⟩

/-- **`Saturate` terminates.**  If every section satisfies the data-flow
    criterion, running all sections to their fixpoints terminates (with a
    finite result). -/
theorem saturate_terminates (K : Ctx B L D) (D₀ : DB B L D) {Stab : Set D → Set D}
    (hS : StabOp Stab) {A : Set D → Set D} (hA : CloOp A) (V : Set D) (hV : V.Finite)
    (hD : D₀.Finite) (lsrc nsrc : L → ℕ → List (Pos B L)) (ok : L → Prop)
    (hK : LetsFlow K V lsrc nsrc A ok) :
    ∀ (secs : List (List (Clause B L D))), (∀ sec ∈ secs, ∀ c ∈ sec, DFClause V K.v₀ ok c) →
      (∀ sec ∈ secs, DFGAcyclic lsrc nsrc Stab sec) →
      ∀ X : Set (Act B L D), X.Finite → ∃ Z, SatRun K D₀ secs X Z ∧ Z.Finite
  | [], _, _, X, hX => ⟨X, .nil, hX⟩
  | sec :: secs, hc, hacyc, X, hX => by
    obtain ⟨n, hfix, hfin⟩ := dfg_terminates K D₀ sec hS hA V hV hD lsrc nsrc ok hK
      (hc sec (List.mem_cons_self ..)) (hacyc sec (List.mem_cons_self ..)) X hX
    obtain ⟨Z, hZ, hZf⟩ := saturate_terminates K D₀ hS hA V hV hD lsrc nsrc ok hK secs
      (fun s hs => hc s (List.mem_cons_of_mem _ hs))
      (fun s hs => hacyc s (List.mem_cons_of_mem _ hs)) _ hfin
    exact ⟨Z, .cons n rfl hfix hZ, hZf⟩

open Classical in
/-- A saturation function: runs `Saturate` whenever the data-flow criterion
    guarantees termination. -/
noncomputable def satFn (secs : List (List (Clause B L D)))
    (K : Ctx B L D) (D₀ : DB B L D) (X : Set (Act B L D)) :
    Set (Act B L D) :=
  if h : ∃ Z, SatRun K D₀ secs X Z ∧ Z.Finite then Classical.choose h else X

theorem satFn_spec (secs : List (List (Clause B L D))) (V : Set D) (hV : V.Finite)
    (lsrc nsrc : L → ℕ → List (Pos B L)) {Stab : Set D → Set D} (hS : StabOp Stab)
    {A : Set D → Set D} (hA : CloOp A)
    (hacyc : ∀ sec ∈ secs, DFGAcyclic lsrc nsrc Stab sec)
    (ok : L → Prop) (K : Ctx B L D) (hK : LetsFlow K V lsrc nsrc A ok)
    (hc : ∀ sec ∈ secs, ∀ c ∈ sec, DFClause V K.v₀ ok c)
    (D₀ : DB B L D) (X : Set (Act B L D)) (hD : D₀.Finite) (hX : X.Finite) :
    SatRun K D₀ secs X (satFn secs K D₀ X) ∧ (satFn secs K D₀ X).Finite := by
  have h := saturate_terminates K D₀ hS hA V hV hD lsrc nsrc ok hK secs hc hacyc X hX
  simp only [satFn, dif_pos h]
  exact Classical.choose_spec h

end Enfflash
