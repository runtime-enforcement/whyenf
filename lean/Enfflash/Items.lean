/-
  EnfFlash formalization — EF items and their evaluation (paper, Section 3,
  Figure 3 and Algorithm 2: `Interp`, `Eval`, and the table updates at the end
  of `Saturate`), and the items emitted by `Compile` (Algorithm 4).

  An item is a `let` (or `filter let`), a `table` with an optional window and
  `add`/`remove` clauses, a `lagged table`, or an `agg let`.  A clause
  `π if φ` is a trigger over `off + ar` local variables: `off` bound ones
  (existentials, aggregated variables), then the item's columns `x̄`; it
  denotes the rows `{v↾x̄ | v ∈ ⟦c⟧_R}` (`rows`).

  * `eval` is `Eval(d, R, T, τ)`, `interp` is `Interp(𝒮)` (the items in order,
    each evaluated on the interpretation of the earlier ones), and
    `updateTables` the table updates of `Saturate`;
  * `items Γ gd cls` are the items realizing the lets `Γ`, with the clauses
    `cls` computed by guard extraction (`ClausesOK`): a `let` (`filter let`
    if unguarded) for a present body, a `table` for a since (add: right
    operand, remove: negated left operand), a `lagged table` for a previous,
    an `agg let` for an aggregation;
  * `interp_eq` and `updateTables_eq`: on these items, `Interp` computes the
    let interpretation `lvOf` and the table updates are `commitTab`; hence the
    loop running the items (`itemParams`) is the loop with concrete tables
    (`itemParams_eq`), for which the end-to-end theorem is proved.
-/
import Enfflash.TableDeps

namespace Enfflash

variable {B D : Type}

/-! ## Items -/

/-- An EF item (Figure 3).  Clauses are triggers over `off + ar` local
    variables, the item's `ar` columns last. -/
inductive Item (B D : Type) where
  /-- `[filter] let p(x̄) := {c}` -/
  | let_ (filter : Bool) (ar off : ℕ) (c : Trigger B ℕ D)
  /-- `table p(x̄) [window a b] := add {add} remove {rem}` (`rem` over the
      columns only) -/
  | table (ar off a : ℕ) (b : Option ℕ) (add rem : Trigger B ℕ D)
  /-- `lagged table p(x̄) [window a b] := add {add}` -/
  | lagged (ar off a : ℕ) (b : Option ℕ) (add : Trigger B ℕ D)
  /-- `agg let p(ḡ, ō) := ω(t̄) group_by ḡ over {c}`: the `k` aggregated
      variables first, the results at the column positions `ys` -/
  | agg (ar k : ℕ) (ω : AggOp D) (ts : List (Term D)) (ys : List ℕ) (c : Trigger B ℕ D)

/-- The number of columns of an item. -/
def Item.ar : Item B D → ℕ
  | let_ _ ar _ _ | table ar _ _ _ _ _ | lagged ar _ _ _ _ | agg ar _ _ _ _ _ => ar

section
variable (v₀ : ℕ → D)

/-- The rows of a clause: `{v↾x̄ | v ∈ ⟦c⟧_R}`, where `R` is the working set
    `W` with the let interpretation `lv`. -/
def rows (off ar : ℕ) (c : Trigger B ℕ D) (W : DB B ℕ D) (lv : ℕ → List D → Prop) :
    Set (List D) :=
  {r | ∃ ls : List D, ls.length = off + ar ∧ c.sat (ptTr W lv) 0 (vapp ls v₀) ∧ r = ls.drop off}

/-- `Eval(d, R, T, τ)` (Algorithm 2) for the item `d` at position `p`:
    a `let` returns the rows of its clause; a `table` its stored rows in the
    window, minus the rows matched by `remove`, plus (if the window starts at
    `0`) the rows matched by `add`; a `lagged table` its stored rows in the
    window; an `agg let` applies `ω` to each group of its `over` clause. -/
def eval (tab : Tab D) (τ : ℕ) (W : DB B ℕ D) (lv : ℕ → List D → Prop) (p : ℕ) :
    Item B D → List D → Prop
  | .let_ _ ar off c, as => as ∈ rows v₀ off ar c W lv
  | .table ar off a b add rem, as =>
    ((∃ τ', (τ', as) ∈ tab.since p ∧ inI a b (τ - τ')) ∧ as ∉ rows v₀ 0 ar rem W lv) ∨
      (a = 0 ∧ as ∈ rows v₀ off ar add W lv)
  | .lagged _ _ a b _, as => ∃ τ', (τ', as) ∈ tab.lag p ∧ inI a b (τ - τ')
  | .agg _ k ω ts ys c, as =>
    aggSem k ω ts ys (vapp as v₀) (fun ds => c.sat (ptTr W lv) 0 (vapp ds (vapp as v₀)))

/-- `R_n` of `Interp` (Algorithm 2): the interpretation of the first `n`
    items, each evaluated on the interpretation of the earlier ones. -/
def interpUpTo (its : List (Item B D)) (tab : Tab D) (τ : ℕ) (W : DB B ℕ D) :
    ℕ → ℕ → List D → Prop
  | 0 => fun _ _ => False
  | n + 1 => fun q as => if q < n then interpUpTo its tab τ W n q as else if q = n then
      (match its[n]? with
       | some it => as.length = it.ar ∧ eval v₀ tab τ W (interpUpTo its tab τ W n) n it as
       | none => False)
      else False

/-- `Interp(𝒮)`: the interpretation of all items on the working set `W`. -/
def interp (its : List (Item B D)) (tab : Tab D) (τ : ℕ) (W : DB B ℕ D) (q : ℕ) :
    List D → Prop :=
  interpUpTo v₀ its tab τ W (q + 1) q

/-- The table updates at the end of `Saturate` (Algorithm 2): a table drops
    the rows matched by `remove` and stores, with timestamp `τ`, the rows
    matched by `add`; a lagged table stores the rows matched by `add`. -/
def updateTables (its : List (Item B D)) (tab : Tab D) (τ : ℕ) (W : DB B ℕ D) : Tab D where
  since n := match its[n]? with
    | some (.table ar off _ _ add rem) =>
      {r | r ∈ tab.since n ∧ r.2 ∉ rows v₀ 0 ar rem W (interp v₀ its tab τ W)} ∪
      {r | r.1 = τ ∧ r.2 ∈ rows v₀ off ar add W (interp v₀ its tab τ W)}
    | _ => ∅
  lag n := match its[n]? with
    | some (.lagged ar off _ _ add) =>
      {r | r.1 = τ ∧ r.2 ∈ rows v₀ off ar add W (interp v₀ its tab τ W)}
    | _ => ∅

end

/-! ## Simplification of residual filters

The compiler simplifies the residual filters left by guard extraction: it
drops `⊤` conjuncts and double negations. -/

/-- `φ ∧ ψ`, dropping a `⊤` conjunct. -/
def Fm.mkConj : Fm B ℕ D → Fm B ℕ D → Fm B ℕ D
  | .tt, ψ => ψ
  | φ, .tt => φ
  | φ, ψ => .conj φ ψ

/-- `¬φ`, eliminating a double negation. -/
def Fm.mkNeg : Fm B ℕ D → Fm B ℕ D
  | .neg φ => φ
  | φ => .neg φ

/-- Simplify a formula: drop `⊤` conjuncts and double negations. -/
def Fm.simp : Fm B ℕ D → Fm B ℕ D
  | .conj φ ψ => Fm.mkConj φ.simp ψ.simp
  | .neg φ => Fm.mkNeg φ.simp
  | .ex φ => .ex φ.simp
  | .ev a b φ => .ev a b φ.simp
  | .nx a b φ => .nx a b φ.simp
  | φ => φ

theorem Tr.sat_mkConj (σ : Tr B ℕ D) (i : ℕ) (v : ℕ → D) (φ ψ : Fm B ℕ D) :
    σ.sat i v (Fm.mkConj φ ψ) ↔ σ.sat i v φ ∧ σ.sat i v ψ := by
  cases φ <;> cases ψ <;> simp [Fm.mkConj, Tr.sat]

theorem Tr.sat_mkNeg (σ : Tr B ℕ D) (i : ℕ) (v : ℕ → D) (φ : Fm B ℕ D) :
    σ.sat i v (Fm.mkNeg φ) ↔ ¬ σ.sat i v φ := by
  cases φ <;> simp [Fm.mkNeg, Tr.sat]

/-- **Simplification preserves the meaning of formulas.** -/
theorem Tr.sat_simp (σ : Tr B ℕ D) (φ : Fm B ℕ D) :
    ∀ i v, σ.sat i v φ.simp ↔ σ.sat i v φ := by
  induction φ with
  | conj φ ψ ih₁ ih₂ => intro i v; rw [Fm.simp, Tr.sat_mkConj, ih₁, ih₂]; rfl
  | neg φ ih => intro i v; rw [Fm.simp, Tr.sat_mkNeg, ih]; rfl
  | ex φ ih => intro i v; simp only [Fm.simp, Tr.sat, ih]
  | ev a b φ ih => intro i v; simp only [Fm.simp, Tr.sat, ih]
  | nx a b φ ih => intro i v; simp only [Fm.simp, Tr.sat, ih]
  | tt | pred | eq => intro i v; rfl

/-! ## The items emitted by `Compile` -/

/-- The clauses of the item realizing a let: the clause of its
    value-producing operand (`val`), and the `remove` clause of a table
    (`rem`). -/
structure LetCl (B D : Type) where
  val : Trigger B ℕ D
  rem : Trigger B ℕ D

/-- The item realizing a let (Algorithm 4) with clauses `c`: a `let` (a
    `filter let` if `filter`) for a present body, a `table` for a since, a
    `lagged table` for a previous, an `agg let` for an aggregation. -/
def itemOf (filter : Bool) (c : LetCl B D) (d : LetDef B ℕ D) : Item B D :=
  match d.body with
  | .now φ => .let_ filter d.arity φ.stripEx.1 c.val
  | .since a b _ φr => .table d.arity φr.stripEx.1 a b c.val c.rem
  | .prev a b φ => .lagged d.arity φ.stripEx.1 a b c.val
  | .agg k ω ts ys _ => .agg d.arity k ω ts ys c.val

/-- The items of the lets `Γ`, in let order: unguarded lets are `filter`
    lets. -/
def items (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D)) (cls : ℕ → LetCl B D) :
    List (Item B D) :=
  Γ.mapIdx fun p d => itemOf (gd p).isNone (cls p) d

theorem items_get (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D))
    (cls : ℕ → LetCl B D) (n : ℕ) :
    (items Γ gd cls)[n]? = Γ[n]?.map (itemOf (gd n).isNone (cls n)) := by
  simp [items, List.getElem?_mapIdx]

theorem itemOf_ar (f : Bool) (c : LetCl B D) (d : LetDef B ℕ D) : (itemOf f c d).ar = d.arity := by
  unfold itemOf; cases d.body <;> rfl

/-- **The clauses are those of `TypeLet`**, computed by joint guard
    extraction (`GXJ`, Figure 5): the clause of a guarded let is its guards `π`
    and the residual filter `φ'` of the extraction from its value-producing
    operand `φ` (an unguarded `filter let` has the clause `if φ`); the
    `remove` clause of a table is `π_r if ¬φ_r'`, extracted from the negated
    left operand for the table's columns.  Filters are simplified
    (`Fm.simp`), as in the compiler. -/
def ClausesOK (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D)) (cls : ℕ → LetCl B D) :
    Prop :=
  ∀ p (d : LetDef B ℕ D), Γ[p]? = some d →
    (∀ φ, d.gop = some φ →
      (∀ π, gd p = some π →
        ∃ φ', GXJ (enumOf gd) d.gvars true φ π φ' ∧ (cls p).val = ⟨π, φ'.simp⟩) ∧
      (gd p = none → (cls p).val = ⟨Guards.top, φ.simp⟩)) ∧
    (∀ a b φl φr, d.body = .since a b φl φr → ∃ πr φr',
      GXJ (enumOf gd) (List.range d.arity) false φl πr φr' ∧
        (cls p).rem = ⟨πr, (Fm.neg φr').simp⟩)

theorem mem_rows (v₀ : ℕ → D) (off ar : ℕ) (c : Trigger B ℕ D) (W : DB B ℕ D)
    (lv : ℕ → List D → Prop) (as : List D) :
    as ∈ rows v₀ off ar c W lv ↔
      as.length = ar ∧ ∃ ds : List D, ds.length = off ∧ c.sat (ptTr W lv) 0 (vapp ds (vapp as v₀)) := by
  constructor
  · rintro ⟨ls, hl, hc, rfl⟩
    refine ⟨by simp [hl], ls.take off, by simp [hl], ?_⟩
    rwa [← vapp_append, List.take_append_drop]
  · rintro ⟨hl, ds, hd, hc⟩
    exact ⟨ds ++ as, by simp [hd, hl], by rwa [vapp_append], by simp [hd]⟩

section
variable {Γ : List (LetDef B ℕ D)} {gd : ℕ → Option (Guards B ℕ D)} {cls : ℕ → LetCl B D}
  (hc : ClausesOK Γ gd cls)
include hc

/-- The clause of a let holds iff its value-producing operand does
    (`GXJ.sound`). -/
theorem val_iff {p : ℕ} {d : LetDef B ℕ D} (hd : Γ[p]? = some d) {φ : Fm B ℕ D}
    (hφ : d.gop = some φ) (σ : Tr B ℕ D) (w : ℕ → D) :
    (cls p).val.sat σ 0 w ↔ σ.sat 0 w φ := by
  rcases hπ : gd p with _ | π
  · rw [((hc p d hd).1 φ hφ).2 hπ]
    simp [Trigger.sat, Tr.sat_simp]
  · obtain ⟨φ', hg, he⟩ := ((hc p d hd).1 φ hφ).1 π hπ
    rw [he]
    have := (GXJ.sound hg).1 σ 0 w
    have ht : Guards.sat σ 0 w ([[]] : Guards B ℕ D) := Guards.sat_top σ 0 w
    simp only [polSat, ht, true_and, if_true] at this
    simp only [Trigger.sat, Tr.sat_simp]; exact this.symm

/-- The `remove` clause of a table holds iff its left operand fails
    (`GXJ.sound`). -/
theorem rem_iff {p : ℕ} {d : LetDef B ℕ D} (hd : Γ[p]? = some d) {a : ℕ} {b : Option ℕ}
    {φl φr : Fm B ℕ D} (hb : d.body = .since a b φl φr) (σ : Tr B ℕ D) (w : ℕ → D) :
    (cls p).rem.sat σ 0 w ↔ ¬ σ.sat 0 w φl := by
  obtain ⟨πr, φr', hg, he⟩ := (hc p d hd).2 a b φl φr hb
  rw [he]
  have := (GXJ.sound hg).1 σ 0 w
  have ht : Guards.sat σ 0 w ([[]] : Guards B ℕ D) := Guards.sat_top σ 0 w
  simp only [polSat, ht, true_and, Bool.false_eq_true, if_false] at this
  simp only [Trigger.sat, Tr.sat_simp, Tr.sat]; exact this.symm

variable (v₀ : ℕ → D)

/-- The rows of the clause of a value-producing operand `φ` (leading
    existentials stripped) are the tuples satisfying `φ`. -/
theorem rows_valOp {p : ℕ} {d : LetDef B ℕ D} (hd : Γ[p]? = some d) {φ : Fm B ℕ D}
    (hφ : d.gop = some φ.stripEx.2) (W : DB B ℕ D) (lv : ℕ → List D → Prop) (as : List D) :
    as ∈ rows v₀ φ.stripEx.1 d.arity (cls p).val W lv ↔
      as.length = d.arity ∧ sat0 v₀ W lv φ as := by
  rw [mem_rows, sat0, Tr.sat_stripEx]
  simp only [val_iff hc hd hφ]

/-- The rows of the `remove` clause of a table are the tuples (of its
    arity) falsifying its left operand. -/
theorem rows_rem {p : ℕ} {d : LetDef B ℕ D} (hd : Γ[p]? = some d) {a : ℕ} {b : Option ℕ}
    {φl φr : Fm B ℕ D} (hb : d.body = .since a b φl φr) (W : DB B ℕ D)
    (lv : ℕ → List D → Prop) (as : List D) :
    as ∈ rows v₀ 0 d.arity (cls p).rem W lv ↔ as.length = d.arity ∧ ¬ sat0 v₀ W lv φl as := by
  rw [mem_rows]
  simp only [List.length_eq_zero_iff, exists_eq_left, vapp_nil, rem_iff hc hd hb, sat0]

/-- `Eval` on the item of a let is the let's value (`bodyVal`). -/
theorem eval_itemOf (tab : Tab D) (τ : ℕ) (W : DB B ℕ D) (lv : ℕ → List D → Prop)
    {p : ℕ} {d : LetDef B ℕ D} (hd : Γ[p]? = some d) (as : List D) (hl : as.length = d.arity) :
    eval v₀ tab τ W lv p (itemOf (gd p).isNone (cls p) d) as ↔
      bodyVal v₀ tab τ W lv p d.body as := by
  unfold itemOf
  cases hb : d.body with
  | now φ =>
    have hφ : d.gop = some φ.stripEx.2 := by simp [LetDef.gop, hb, LBody.valOp]
    simp only [eval, bodyVal, rows_valOp hc v₀ hd hφ, hl, true_and]
  | since a b φl φr =>
    have hφ : d.gop = some φr.stripEx.2 := by simp [LetDef.gop, hb, LBody.valOp]
    have hrem : as ∉ rows v₀ 0 d.arity (cls p).rem W lv ↔ sat0 v₀ W lv φl as := by
      rw [rows_rem hc v₀ hd hb]; simp [hl]
    simp only [eval, bodyVal, rows_valOp hc v₀ hd hφ, hl, true_and, hrem]
    constructor
    · rintro (⟨⟨τ', h, hI⟩, hl'⟩ | ⟨rfl, hr⟩)
      · exact ⟨τ', Or.inl ⟨h, hl'⟩, hI⟩
      · exact ⟨τ, Or.inr ⟨rfl, hr⟩, by simp [inI]⟩
    · rintro ⟨τ', h | ⟨rfl, hr⟩, hI⟩
      · exact Or.inl ⟨⟨τ', h.1, hI⟩, h.2⟩
      · exact Or.inr ⟨by simpa [inI] using hI.1, hr⟩
  | prev a b φ => rfl
  | agg k ω ts ys φ =>
    have hφ : d.gop = some φ := by simp [LetDef.gop, hb]
    simp only [eval, bodyVal]
    exact aggSem_congr (fun ds _ => val_iff hc hd hφ _ _) (fun _ _ => rfl) rfl

/-- **`Interp` computes the let interpretation**: on the items of `Γ`, the
    interpretation `R_n` of `Interp` is that of the lets. -/
theorem interpUpTo_eq (tab : Tab D) (τ : ℕ) (W : DB B ℕ D) :
    ∀ n, interpUpTo v₀ (items Γ gd cls) tab τ W n = lvUpTo Γ v₀ tab τ W n
  | 0 => rfl
  | n + 1 => by
    funext q as
    simp only [interpUpTo, lvUpTo, interpUpTo_eq tab τ W n, items_get]
    split_ifs with h1 h2
    · rfl
    · subst h2
      rcases hd : Γ[q]? with _ | d
      · rfl
      · simp only [Option.map_some, itemOf_ar]
        exact propext (and_congr_right fun hl => eval_itemOf hc v₀ tab τ W _ hd as hl)
    · rfl

theorem interp_eq (tab : Tab D) (τ : ℕ) (W : DB B ℕ D) :
    interp v₀ (items Γ gd cls) tab τ W = lvOf Γ v₀ tab τ W := by
  funext q; exact congrFun (interpUpTo_eq hc v₀ tab τ W (q + 1)) q

/-- **The table updates of `Saturate` are `commitTab`.** -/
theorem updateTables_eq (tab : Tab D) (τ : ℕ) (W : DB B ℕ D) :
    updateTables v₀ (items Γ gd cls) tab τ W = commitTab Γ v₀ tab τ W := by
  have hI := interp_eq hc v₀ tab τ W
  have hsince : ∀ n, (updateTables v₀ (items Γ gd cls) tab τ W).since n =
      (commitTab Γ v₀ tab τ W).since n := by
    intro n
    simp only [updateTables, commitTab, items_get, hI]
    rcases hd : Γ[n]? with _ | ⟨ar, body⟩
    · rfl
    · simp only [Option.map_some]
      unfold itemOf
      cases hb : body with
      | since a b φl φr =>
        have hb' : (⟨ar, body⟩ : LetDef B ℕ D).body = .since a b φl φr := hb
        have hφ : (⟨ar, body⟩ : LetDef B ℕ D).gop = some φr.stripEx.2 := by
          simp [LetDef.gop, hb, LBody.valOp]
        ext r
        simp only [Set.mem_union, Set.mem_setOf_eq]
        rw [rows_valOp hc v₀ (d := ⟨ar, body⟩) hd hφ, rows_rem hc v₀ (d := ⟨ar, body⟩) hd hb']
        simp only [sat0]
        constructor
        · rintro (⟨h, hn⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨h, fun hl => by by_contra hc'; exact hn ⟨hl, hc'⟩⟩
          · exact Or.inr ⟨h1, h2⟩
        · rintro (⟨h, hk⟩ | ⟨h1, h2⟩)
          · exact Or.inl ⟨h, fun ⟨hl, hn⟩ => hn (hk hl)⟩
          · exact Or.inr ⟨h1, h2⟩
      | _ => rfl
  have hlag : ∀ n, (updateTables v₀ (items Γ gd cls) tab τ W).lag n =
      (commitTab Γ v₀ tab τ W).lag n := by
    intro n
    simp only [updateTables, commitTab, items_get, hI]
    rcases hd : Γ[n]? with _ | ⟨ar, body⟩
    · rfl
    · simp only [Option.map_some]
      unfold itemOf
      cases hb : body with
      | prev a b φ =>
        have hφ : (⟨ar, body⟩ : LetDef B ℕ D).gop = some φ.stripEx.2 := by
          simp [LetDef.gop, hb, LBody.valOp]
        ext r
        simp only [Set.mem_setOf_eq]
        rw [rows_valOp hc v₀ (d := ⟨ar, body⟩) hd hφ]
      | _ => rfl
  cases h : updateTables v₀ (items Γ gd cls) tab τ W with
  | mk s l =>
    cases h' : commitTab Γ v₀ tab τ W with
    | mk s' l' =>
      rw [h, h'] at hsince hlag
      simp only [Tab.mk.injEq]
      exact ⟨funext hsince, funext hlag⟩

end

/-! ## The loop running the items -/

/-- The enforcement loop of Algorithm 1 running the EF program: the items of
    the lets (evaluated by `Interp`, tables updated as in `Saturate`) and the
    rules `P`. -/
def itemParams (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D)) (cls : ℕ → LetCl B D)
    (v₀ : ℕ → D) (τ : ℕ → ℕ) (inDB : ℕ → DB B ℕ D) (P : Program B ℕ D)
    (Sat : Ctx B ℕ D → DB B ℕ D → Set (Act B ℕ D) → Set (Act B ℕ D)) : LoopParams B ℕ D where
  τ := τ
  inDB := inDB
  P := P
  TS := Tab D
  tab₀ := ⟨fun _ => ∅, fun _ => ∅⟩
  inv := TabInv Γ
  ctx tab t := ⟨fun W => interp v₀ (items Γ gd cls) tab t W, v₀⟩
  commit := updateTables v₀ (items Γ gd cls)
  Sat := Sat

/-- **The loop running the EF items is the loop with concrete tables.** -/
theorem itemParams_eq {Γ : List (LetDef B ℕ D)} {gd : ℕ → Option (Guards B ℕ D)}
    {cls : ℕ → LetCl B D} (hc : ClausesOK Γ gd cls) (v₀ : ℕ → D) (τ : ℕ → ℕ)
    (inDB : ℕ → DB B ℕ D) (P : Program B ℕ D)
    (Sat : Ctx B ℕ D → DB B ℕ D → Set (Act B ℕ D) → Set (Act B ℕ D)) :
    itemParams Γ gd cls v₀ τ inDB P Sat = tableParams Γ v₀ τ inDB P Sat := by
  have hctx : (fun tab t => (⟨fun W => interp v₀ (items Γ gd cls) tab t W, v₀⟩ : Ctx B ℕ D)) =
      fun tab t => ⟨fun W => lvOf Γ v₀ tab t W, v₀⟩ := by
    funext tab t
    rw [show (fun W => interp v₀ (items Γ gd cls) tab t W) = fun W => lvOf Γ v₀ tab t W
      from funext fun W => interp_eq hc v₀ tab t W]
  have hu : updateTables v₀ (items Γ gd cls) = commitTab Γ v₀ := by
    funext tab t W; exact updateTables_eq hc v₀ tab t W
  simp only [itemParams, tableParams, hctx, hu]

end Enfflash
