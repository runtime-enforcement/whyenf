/-
  §4.5 Dependency analysis (main.tex l.1470–1581, Figures 7 and 8).

  Both checks are given relative to the lets `ℒ` of the let-normal form: the
  EDG decomposes let atoms into the events defining them, and the DFG needs
  to know which let columns are aggregation results.  The paper leaves `ℒ`
  implicit.
-/
import Paper.Generate

namespace Paper

variable {Voc : Vocabulary}

/-! ## Atoms occurring in triggers -/

/-- The atoms `e(t̄)` occurring in a formula. -/
def Formula.atoms : Formula Voc → Set (Voc.ℰ × List (Term Voc))
  | .top => ∅
  | .pred e ts => {(e, ts)}
  | .neg φ => φ.atoms
  | .and φ ψ => φ.atoms ∪ ψ.atoms
  | .ex _ φ => φ.atoms
  | .next _ φ => φ.atoms
  | .prev _ φ => φ.atoms
  | .eventually _ φ => φ.atoms
  | .since _ φ ψ => φ.atoms ∪ ψ.atoms
  | .letin _ _ φ ψ => φ.atoms ∪ ψ.atoms
  | .agg _ _ _ _ φ => φ.atoms
  | .eq _ _ => ∅

/-- The event names occurring in a formula. -/
def Formula.preds (φ : Formula Voc) : Set Voc.ℰ := Prod.fst '' φ.atoms

/-- The trigger `θ = (π, ψ)` of a clause as a formula `⋁π ∧ ψ`. -/
def EClause.trig (c : EClause Voc) : Formula Voc := .and c.π.toFormula c.ψ

/-- The atoms `e(t̄)` of the trigger `(π, ψ)`: those of the guards `π` and those
    of the filter `ψ`. -/
def EClause.trigAtoms (c : EClause Voc) : Set (Voc.ℰ × List (Term Voc)) :=
  {a | ∃ κ ∈ c.π, GAtom.pred a.1 a.2 ∈ κ} ∪ c.ψ.atoms

/-- The events occurring in the trigger. -/
def EClause.trigPreds (c : EClause Voc) : Set Voc.ℰ := Prod.fst '' c.trigAtoms

/-! ## Lets -/

/-- `p` is let-bound in `ℒ`. -/
def IsLet (ℒ : List (LetDef Voc)) (p : Voc.ℰ) : Prop := ∃ d ∈ ℒ, d.e = p

/-- "let atoms are decomposed [into] the events defining them" (l.1479):
    `Decomp ℒ q e` if `q` is the base event `e`, or `q` is let-bound and one of
    the events of its body decomposes into `e`. -/
inductive Decomp (ℒ : List (LetDef Voc)) : Voc.ℰ → Voc.ℰ → Prop
  | base {e : Voc.ℰ} : ¬ IsLet ℒ e → Decomp ℒ e e
  | let_ {d : LetDef Voc} {q e : Voc.ℰ} : d ∈ ℒ → q ∈ d.φ.preds → Decomp ℒ q e → Decomp ℒ d.e e

/-! ## Cause/suppress conflicts (l.1477–1496) -/

section EDG
variable (ℒ : List (LetDef Voc)) (R : Set (EClause Voc))

/-- The edge `e → e'` of the Event Dependency Graph, labelled `c^a` (l.1477–1482):
    `e` occurs in the trigger of the clause `c` (let atoms decomposed), and
    `e'` occurs in its effect with polarity `a`.  The vertices are the base
    and obligation events, i.e. the event names that are not let-bound. -/
def EDGEdge (c : EClause Voc) (a : Mode) (e e' : Voc.ℰ) : Prop :=
  c ∈ R ∧ (∃ q ∈ c.trigPreds, Decomp ℒ q e) ∧ c.ε.name = e' ∧ ¬ IsLet ℒ e' ∧ c.ε.pol = a

/-- The EDG, forgetting labels. -/
def EDG (e e' : Voc.ℰ) : Prop := ∃ c a, EDGEdge ℒ R c a e e'

/-- Reachability in the EDG. -/
def Reach : Voc.ℰ → Voc.ℰ → Prop := Relation.ReflTransGen (EDG ℒ R)

/-- `e` and `e'` are in the same strongly connected component. -/
def SameSCC (e e' : Voc.ℰ) : Prop := Reach ℒ R e e' ∧ Reach ℒ R e' e

/-- `e₀` is in an SCC *strictly before* `e`: the SCC of `e₀` precedes the SCC of
    `e` in the condensed graph, i.e. `e`'s SCC is reachable from it
    (NOTES.md, N8). -/
def SCCBefore (e₀ e : Voc.ℰ) : Prop := Reach ℒ R e₀ e ∧ ¬ Reach ℒ R e e₀

end EDG

/-- `σ₁` and `σ₂` have the same timestamps and agree on the events with a name
    in `N`. -/
def Str.AgreeOn (σ₁ σ₂ : Str Voc.toSignature) (N : Set Voc.ℰ) : Prop :=
  σ₁.τ = σ₂.τ ∧ ∀ j (ev : Event Voc.toSignature), ev.e ∈ N → (ev ∈ σ₁.D j ↔ ev ∈ σ₂.D j)

/-- `let e₁(x̄₁) = φ₁ in … let e_m(x̄_m) = φ_m in φ`: a trigger evaluated with
    its let atoms interpreted by the lets of `ℒ`. -/
def withLets (ℒ : List (LetDef Voc)) (φ : Formula Voc) : Formula Voc :=
  ℒ.foldr (fun d acc => .letin d.e d.xs d.φ acc) φ

/-- The SMT query of l.1485–1490: `θ_ℂ ∧ θ_𝕊` is satisfiable "by only taking into
    account events from SCCs (strictly) before `e`".  Read as (NOTES.md, N8):
    * the two clauses are renamed apart (two valuations `v₁`, `v₂`), and the
      caused and suppressed events coincide (`⟦t̄₁⟧_{v₁} = ⟦t̄₂⟧_{v₂}`);
    * `shared = some N`: the triggers are evaluated at the same time-point on
      two structures that agree on the events with a name in `N`, i.e. the
      events of other SCCs may be different in the two evaluations;
    * `shared = none` (a deferred effect, l.1490): "the two triggers are
      evaluated at different time-points, and no event is shared". -/
def PairSat (ℒ : List (LetDef Voc)) (shared : Option (Set Voc.ℰ)) (c₁ c₂ : EClause Voc) : Prop :=
  ∃ (σ₁ σ₂ : Str Voc.toSignature) (i₁ i₂ : ℕ) (v₁ v₂ : Val Voc),
    (match shared with
     | some N => σ₁.AgreeOn σ₂ N ∧ i₁ = i₂
     | none => True) ∧
    v₁.Covers c₁.trig.fv ∧ v₂.Covers c₂.trig.fv ∧
    (withLets ℒ c₁.trig).sat σ₁ v₁ i₁ ∧ (withLets ℒ c₂.trig).sat σ₂ v₂ i₂ ∧
    ∃ ds, Term.evalList v₁ c₁.ε.args = some ds ∧ Term.evalList v₂ c₂.ε.args = some ds

/-- The cause/suppress check (l.1483–1493): for each `e` that one clause `c₁`
    causes and another clause `c₂` suppresses, the query `(θ_ℂ, θ_𝕊)` is
    unsatisfiable; any Sat result rejects the clause set. -/
def ConflictCheck (ℒ : List (LetDef Voc)) (R : Set (EClause Voc)) : Prop :=
  ∀ c₁ ∈ R, ∀ c₂ ∈ R, c₁.ε.pol = .C → c₂.ε.pol = .S → c₁.ε.name = c₂.ε.name →
    ¬ PairSat ℒ
      (if c₁.ε.deferred then none else some {e₀ | SCCBefore ℒ R e₀ c₁.ε.name}) c₁ c₂

/-! ## Termination (l.1553–1565) -/

/-- The nodes `e.i` of the Data-Flow Graph: event arguments. -/
abbrev Pos (Voc : Vocabulary) := Voc.ℰ × ℕ

mutual
/-- The function symbols of a term. -/
def Term.funs : Term Voc → Set Voc.𝔽
  | .var _ => ∅
  | .const _ => ∅
  | .app f ts => {f} ∪ Term.funsList ts
def Term.funsList : List (Term Voc) → Set Voc.𝔽
  | [] => ∅
  | t :: ts => Term.funs t ∪ Term.funsList ts
end

/-- The edge `e.i → e'.j` of the DFG contributed by the clause `c` with
    effect argument `t = t'_j` (l.1554–1557): the trigger mentions
    `e(…, tᵢ = x, …)`, the effect is `e'(…, t'_j, …)`, and `x` occurs in
    `t'_j`.  "Mentions" is any occurrence in `π` or `ψ`; the effect may have
    any polarity (Figure 8 shows the edge of `(use(d), ⊤) ⇒ ¬use(d)`).  Let atoms
    are not decomposed; data flow through lets is given by `LetEdge`. -/
def DFGEdge (R : Set (EClause Voc)) (c : EClause Voc) (t : Term Voc) (q q' : Pos Voc) : Prop :=
  c ∈ R ∧ ∃ x : Voc.𝕍, (∃ ts, (q.1, ts) ∈ c.trigAtoms ∧ ts[q.2]? = some (.var x)) ∧
    q'.1 = c.ε.name ∧ c.ε.args[q'.2]? = some t ∧ x ∈ t.vars

/-- The edge `e.k → p.i` through the let `p(x̄) := φ` of `ℒ` (§4.5): an atom
    `e(…, t_k = z, …)` of the body `φ` binds `z`, and the `i`-th column `xᵢ` of
    `p` is `z` or, for an aggregation `ȳ ← ω(s̄; ḡ) ψ`, a result `xᵢ ∈ ȳ`. -/
def LetEdge (ℒ : List (LetDef Voc)) (q q' : Pos Voc) : Prop :=
  ∃ d ∈ ℒ, q'.1 = d.e ∧ ∃ y, d.xs[q'.2]? = some y ∧ ∃ ts, (q.1, ts) ∈ d.φ.atoms ∧
    ∃ z : Voc.𝕍, ts[q.2]? = some (.var z) ∧
      (z = y ∨ ∃ ys ω ss gs ψ, d.φ = .agg ys ω ss gs ψ ∧ y ∈ ys)

/-- The DFG, forgetting labels: the edges of the clauses and of the lets. -/
def DFG (ℒ : List (LetDef Voc)) (R : Set (EClause Voc)) (q q' : Pos Voc) : Prop :=
  (∃ c t, DFGEdge R c t q q') ∨ LetEdge ℒ q q'

/-- The values obtained by applying the functions `F` repeatedly to `V`. -/
inductive Closure (F : Set Voc.𝔽) (V : Set Voc.𝔻) : Voc.𝔻 → Prop
  | base {d : Voc.𝔻} : d ∈ V → Closure F V d
  | app {f : Voc.𝔽} (a : Fin (Voc.ιF f) → Voc.𝔻) : f ∈ F → (∀ k, Closure F V (a k)) →
      Closure F V (Voc.fhat f a)

/-- The fixed preorder `≼` on `𝔻` w.r.t. which stability is defined (§4.5):
    every value has finitely many predecessors. -/
structure StabOrder (Voc : Vocabulary) where
  le : Voc.𝔻 → Voc.𝔻 → Prop
  trans : ∀ a b c, le a b → le b c → le a c
  finDown : ∀ d, {d' | le d' d}.Finite

/-- `f` is *stable* w.r.t. `≼`: `f̂(ā) ≼ aₖ` for some argument `aₖ`.  (A
    0-ary `f` is therefore never stable.) -/
def Stable (O : StabOrder Voc) (f : Voc.𝔽) : Prop :=
  ∀ a : Fin (Voc.ιF f) → Voc.𝔻, ∃ k, O.le (Voc.fhat f a) (a k)

/-- `e.i` is an aggregation result: `e` is bound by `ℒ` to an aggregation
    `ȳ ← ω(s̄; ḡ) ψ` and its `i`-th column is one of the results `ȳ`. -/
def AggResult (ℒ : List (LetDef Voc)) (q : Pos Voc) : Prop :=
  ∃ d ∈ ℒ, d.e = q.1 ∧ ∃ ys ω ss gs ψ, d.φ = .agg ys ω ss gs ψ ∧ ∃ y ∈ ys, d.xs[q.2]? = some y

/-- An edge is *stable* iff it does not pass through an aggregation result and
    all function symbols in `t'_j` are stable (l.1558–1560).  "Passes through
    an aggregation result" is read as: its source or its target is one. -/
def StableEdge (O : StabOrder Voc) (ℒ : List (LetDef Voc)) (t : Term Voc) (q q' : Pos Voc) :
    Prop :=
  ¬ AggResult ℒ q ∧ ¬ AggResult ℒ q' ∧ ∀ f ∈ t.funs, Stable O f

/-- The termination check (l.1561): no non-stable edge lies on a cycle.  A let
    edge copies values; it is stable iff it does not touch an aggregation
    result. -/
def DFGCheck (O : StabOrder Voc) (ℒ : List (LetDef Voc)) (R : Set (EClause Voc)) : Prop :=
  (∀ c t q q', DFGEdge R c t q q' → ¬ StableEdge O ℒ t q q' →
    ¬ Relation.ReflTransGen (DFG ℒ R) q' q) ∧
  (∀ q q', LetEdge ℒ q q' → (AggResult ℒ q ∨ AggResult ℒ q') →
    ¬ Relation.ReflTransGen (DFG ℒ R) q' q)

end Paper
