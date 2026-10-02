/-
  §4.6 Compilation (main.tex l.1583–1677, Algorithm 4, Theorem 4.3).
-/
import Paper.Dependency
import Paper.EFSemantics

namespace Paper

variable {Voc : Vocabulary}

/-! ## The topological order `≺` (l.1590–1592) -/

/-- A topological order `≺` on the condensed SCCs of the EDG, sources first,
    given by a rank: two events have the same rank iff they are in the same
    SCC, and edges do not decrease the rank.  It "also induces an order on
    clauses", by the rank of the effect's event. -/
def TopoOrder (ℒ : List (LetDef Voc)) (R : Set (EClause Voc)) (rk : Voc.ℰ → ℕ) : Prop :=
  (∀ e e', SameSCC ℒ R e e' ↔ rk e = rk e') ∧ ∀ e e', EDG ℒ R e e' → rk e ≤ rk e'

/-! ## From MFOTL triggers to EF clauses

§4.6: a trigger `(π, ψ)` becomes `π if ψ`, or `if ψ` if `π = {⊤}`; compilation
fails if a trigger or filter has no EF counterpart.  The translations below
are therefore partial. -/

/-- A guard argument `id ∣ v`. -/
def Term.toGArg : Term Voc → Option (GArg Voc)
  | .var x => some (.var x)
  | .const c => some (.val c)
  | .app .. => none

/-- A guard atom `id(id ∣ v, …)` or `id == v`. -/
def GAtom.toAtom : GAtom Voc → Option (Atom Voc)
  | .pred p ts => (ts.mapM Term.toGArg).map (.pred p)
  | .eq x c => some (.eq x c)

def toNList {α : Type} : List α → Option (NList α)
  | [] => none
  | a :: l => some ⟨a, l⟩

/-- `π ::= κ (or κ)*` with `κ ::= γ (& γ)*`: `π` and every `κ` must be non-empty. -/
def GDisj.toEGuards (π : GDisj Voc) : Option (EGuards Voc) := do
  let κs ← π.mapM fun κ => do toNList (← κ.mapM GAtom.toAtom)
  toNList κs

/-- EF filters `true ∣ id(t̄) ∣ φ & φ ∣ !φ` (`⊥`, `∨`, `→` are abbreviations). -/
def Formula.toFilter : Formula Voc → Option (Filter Voc)
  | .top => some .tt
  | .pred p ts => some (.pred p ts)
  | .neg φ => .not <$> φ.toFilter
  | .and φ ψ => .and <$> φ.toFilter <*> ψ.toFilter
  | _ => none

/-- `π if ψ`; the trigger `({⊤}, ψ)` is the unguarded clause `if ψ`. -/
def toClause (π : GDisj Voc) (ψ : Formula Voc) : Option (Clause Voc) :=
  match π with
  | [[]] => .filter <$> ψ.toFilter
  | _ => do pure (.guarded (← π.toEGuards) (some (← ψ.toFilter)))

/-- `[n, b]` for an interval `I = [n, b]` (every interval is one,
    `Interval.eq_icc`). -/
noncomputable def Interval.bounds (I : Interval) : ℕ × ℕ∞ :=
  open Classical in
  if h : ∃ a b hab, I = Interval.icc a b hab then (h.choose, h.choose_spec.choose) else (0, ⊤)

/-! ## Algorithm 4 -/

section
open Classical

/-- The item realizing the body of the let `p(x̄) := φ` (Algorithm 4, line 4):
    "`table` (past operator), `agg`, or `filter let` (non-guarded present) or
    `let`", as detailed in §4.6:
    * `⧫_I φ` ↦ `table p(x̄) [window I] := add {θ}`,
    * `●_I φ` ↦ `lagged table p(x̄) [window I] := add {θ}`,
    * `φ_l S_I φ_r` ↦ `table p(x̄) [window I] := add {θ_r} remove {θ_l}`,
    * `ȳ ← ω(s̄; ḡ) φ` ↦ `agg let p(ḡ ȳ) := ω(s̄) group_by ḡ over {θ}`
      (requires `x̄ = ḡ ȳ`, the column order of EF aggregations, with no
      repeated variable; NOTES.md, N6),
    * a present body ↦ `let p(x̄) := {θ}`, or `filter let p(x̄) := {if χ}` if `p`
      is filter-only,
    where the `θ`s are the guards that `TypeLet` computes, with `m = m_Γ`
    (recomputed here: `Γ` does not record them; NOTES.md, F9).  The `∃ȳ` of a
    body `∃ȳ. χ` is realized by the projection `v↾x̄`. -/
noncomputable def letItem (Ξ : RwSetting Voc) (Γ : LetCtx Voc) (colTy : Voc.𝕍 → Ty) (d : LetDef Voc) :
    Option (Item Voc) :=
  let m : Set Voc.ℰ := Ξ.m Γ
  let χ := stripExists d.φ
  let X : Set Voc.𝕍 := {x | x ∈ d.xs} ∪ χ.fv
  let cols := d.xs.map fun x => (⟨x, colTy x⟩ : Col Voc)
  let cl (θ : Option (GDisj Voc × Formula Voc)) : Option (Clause Voc) :=
    θ.bind fun θ => toClause θ.1 θ.2
  match χ with
  | .since I .top φ => do
    pure (.table none false d.e cols (some I.bounds) (← cl (Guards m φ.fv φ)) none)
  | .prev I φ => do
    pure (.table none true d.e cols (some I.bounds) (← cl (Guards m φ.fv φ)) none)
  | .agg ys ω ss gs φ =>
    if d.xs = gs ++ ys ∧ (gs ++ ys).Nodup then do
      pure (.agg none d.e cols ω ss gs (← cl (Guards m φ.fv φ)))
    else none
  | .since I φl φr => do
    pure (.table none false d.e cols (some I.bounds) (← cl (Guards m X φr))
      (some (← cl (Guards m X (.neg φl)))))
  | _ =>
    match Γ d.e with
    | some (false, _, _) => do pure (.let_ none true d.e cols (.filter (← χ.toFilter)))
    | _ => do pure (.let_ none false d.e cols (← cl (Guards m X χ)))

/-- The rule `[±] ε̂ := trigger {π if ψ}` for a clause `(π, ψ) ⇒ ε` (line 7): `+`
    for a caused, `−` for a suppressed effect; `ε̂` carries `[delay n]` if `ε` is
    `◇_[n,n] p(…)` and `[next n]` if `ε` is `○…○ p(…)` with `n` `○`.  A `◇_I` with
    `I` not of the form `[n, n]` has no rule. -/
noncomputable def ruleItem (c : EClause Voc) : Option (Item Voc) := do
  let trig ← toClause c.π c.ψ
  match c.ε with
  | .cau e ts => pure (.rule none .plus e ts none none trig)
  | .sup e ts => pure (.rule none .minus e ts none none trig)
  | .ev I e ts =>
    if h : ∃ n : ℕ, I = Interval.icc n n le_rfl then
      pure (.rule none .plus e ts (some h.choose) none trig)
    else none
  | .nexts n e ts => pure (.rule none .plus e ts none (some n) trig)

/-- Lines 5–8: the rules, by SCC in order `≺`; "open a `section` for the SCC
    if not already open", a `fixpoint` section.  `cur` is the rank of the
    open section. -/
def withSections (rk : Voc.ℰ → ℕ) : Option ℕ → List (EClause Voc × Item Voc) → List (Item Voc)
  | _, [] => []
  | cur, (c, it) :: rest =>
    if cur = some (rk c.ε.name) then it :: withSections rk cur rest
    else .sec .fixpoint :: it :: withSections rk (some (rk c.ε.name)) rest

/-- The non-let events of the triggers and effects of `rs`, as a list. -/
noncomputable def evDecls (ℒ : List (LetDef Voc)) (rs : List (EClause Voc)) : List Voc.ℰ :=
  haveI := Voc.finE
  {e | ∃ c ∈ rs, (e ∈ c.trigPreds ∨ e = c.ε.name) ∧ ¬ IsLet ℒ e}.toFinite.toFinset.toList

/-- `Compile(ℒ, Γ, R, ≺)` (Algorithm 4), with `≺` given by the rank `rk`.
    It also takes the setting `Ξ` (for `m_Γ`), an enumeration `rs` of `R` (the
    order of the clauses inside an SCC is not given), and the EF types of
    events and columns, which do not affect the semantics (NOTES.md, F9, F10).  `none` if some let or clause
    has no EF syntax.

    Line 2, "declaration of all base/obligation events in `R`": the
    non-let events of the triggers and effects of `R`. -/
noncomputable def Compile (Ξ : RwSetting Voc) (ℒ : List (LetDef Voc)) (Γ : LetCtx Voc) (rs : List (EClause Voc))
    (rk : Voc.ℰ → ℕ) (evTys : Voc.ℰ → List Ty) (colTy : Voc.𝕍 → Ty) : Option (Program Voc) := do
  let decls := (evDecls ℒ rs).map fun e => (⟨e, evTys e⟩ : EvDecl Voc)
  -- lines 3–5: `for all p ∈ Γ`, in the order of `ℒ`
  let lets ← (ℒ.filter fun d => (Γ d.e).isSome).mapM (letItem Ξ Γ colTy)
  -- lines 6–9
  let sorted := rs.mergeSort fun c c' => decide (rk c.ε.name ≤ rk c'.ε.name)
  let rules ← sorted.mapM fun c => (c, ·) <$> ruleItem c
  pure ⟨decls, none, [], [], lets ++ withSections rk none rules⟩

end

/-! ## The enforcer of an EF program

§3.2 says that Algorithm 2 "defines the behavior of the `μ` and `ν`
functions" (l.848–850).  `mu`, `nu` are partial (a `fixpoint` section may
not terminate) and return sets of rows rather than databases in `𝔻𝔹_ℂ`, `𝔻𝔹_𝕊`.
The enforcer below has a failure state `none`: it is entered when `μ` or `ν`
is undefined, or returns a set that is not in `𝔻𝔹_ℂ` (resp. `𝔻𝔹_𝕊`), and it is
absorbing.  `P` *is* an enforcer on a run iff the run never enters it. -/

section
open Classical

/-- The events `(e, ā)` of `A`, as a database. -/
def REv.toDB (A : Set (REv Voc)) : DB Voc.toSignature := {ev | (ev.e, ev.args) ∈ A}

/-- `A ∈ 𝔻𝔹_E`: every element is an event (right arity) with name in `E`. -/
def REv.InDB (A : Set (REv Voc)) (E : Set Voc.ℰ) : Prop :=
  ∀ x ∈ A, x.1 ∈ E ∧ x.2.length = Voc.ι x.1


/-- The initial state `s₀`: empty tables and no obligations. -/
def EState.init : EState Voc := ⟨fun _ => ∅, fun _ => ∅, ∅⟩

/-- The enforcer `(𝒮, s₀, μ, ν)` defined by `P` for `ℂ`, `𝕊`. -/
noncomputable def Program.enforcer (P : Program Voc) (Cau Sup : Set Voc.ℰ) :
    Enforcer Voc.toSignature Cau Sup where
  𝒮 := Option (EState Voc)
  s₀ := some EState.init
  μ s σ τ D :=
    let fail : Option (EState Voc) × DBOf Voc.toSignature Cau × DBOf Voc.toSignature Sup :=
      (none, ⟨∅, fun _ h => absurd h (Set.notMem_empty _)⟩,
        ⟨∅, fun _ h => absurd h (Set.notMem_empty _)⟩)
    match s with
    | none => fail
    | some st =>
      match mu P st σ τ (Event.raw '' D) with
      | some (st', C, S) =>
        if h : REv.InDB C Cau ∧ REv.InDB S Sup then
          (some st', ⟨REv.toDB C, fun _ hev => (h.1 _ hev).1⟩, ⟨REv.toDB S, fun _ hev => (h.2 _ hev).1⟩)
        else fail
      | none => fail
  ν s σ τ :=
    match s with
    | none => (none, none)
    | some st =>
      match nu P st σ τ with
      | some (st', none) => (some st', none)
      | some (st', some C) =>
        if h : REv.InDB C Cau then (some st', some ⟨REv.toDB C, fun _ hev => (h _ hev).1⟩)
        else (none, none)
      | none => (none, none)

end

/-- `P` is a sound enforcer for a closed `φ` (l.674–677; NOTES.md, N4) on the
    admissible input traces: on every admissible infinite input, `P` defines
    `μ` and `ν` at every call of Algorithm 1 (the failure state is never
    entered; NOTES.md, F5) and the output satisfies `φ`. -/
def Program.SoundEnforcer (P : Program Voc) (Cau Sup : Set Voc.ℰ)
    (Adm : Trace Voc.toSignature → Prop) (φ : Formula Voc) : Prop :=
  φ.fv = ∅ → ∀ σ : Trace Voc.toSignature, σ.length = ⊤ → Adm σ →
    (∀ k st, (P.enforcer Cau Sup).run σ k = some st → st.1.isSome) ∧
    ∃ σ', (P.enforcer Cau Sup).out σ = some σ' ∧ φ.satTr σ' Val.empty 0

/-- The atoms of `φ` have the arity of their event. -/
def Formula.WellArity (φ : Formula Voc) : Prop := ∀ a ∈ φ.atoms, a.2.length = Voc.ι a.1

/-- The arguments of the atoms of `φ` evaluate whenever their variables are
    assigned, i.e. the function symbols are applied with their arity `ι_F`
    (implicit in the paper, which only writes well-formed terms; NOTES.md, N1). -/
def Formula.FunOK (φ : Formula Voc) : Prop :=
  ∀ a ∈ φ.atoms, ∀ v : Val Voc, v.Covers (Term.varsList a.2) → (Term.evalList v a.2).isSome

/-- `φ` is *clean* in the context `G`: no bound variable of `φ` is free in `G`,
    in a sibling subformula, or bound twice on a path.  Figure 5 is unsound
    for formulas that are not clean: suppressing `B(x) ∧ ∃x. A(x)` yields the
    clause `(A(x), B(x)) ⇒ ¬A(x)`, which confuses the two `x` (NOTES.md, N6). -/
def Formula.Clean : Formula Voc → Set Voc.𝕍 → Prop
  | .top, _ | .pred _ _, _ | .eq _ _, _ | .agg .., _ => True
  | .neg φ, G => φ.Clean G
  | .and φ ψ, G => φ.Clean (G ∪ ψ.fv) ∧ ψ.Clean (G ∪ φ.fv)
  | .ex x φ, G => x ∉ G ∧ φ.Clean (G ∪ {x})
  | .next _ φ, G | .prev _ φ, G | .eventually _ φ, G => φ.Clean G
  | .since _ φ ψ, G => φ.Clean (G ∪ ψ.fv) ∧ ψ.Clean (G ∪ φ.fv)
  | .letin _ _ _ ψ, G => ψ.Clean G

/-- Well-formedness of `□φ` and its let-normal form `L`, implicit in the paper
    (NOTES.md, N1, N6):
    * the let names are distinct and fresh (not causable, suppressable, base
      events, or events of `φ`);
    * a let `p(x̄) := φ` has distinct parameters `x̄`, exactly the free variables
      `x̄`, arity `|x̄|`, and
      its body mentions only base events and earlier lets;
    * the formulas `χᵢ` are closed, and all formulas are clean;
    * the atoms have the arity of their events, the aggregations the arity
      of their operators, and the function symbols in atoms their arity;
    * the obligation events `Cau_p`, `Sup_p` are fresh ("fresh obligation
      event", l.1286), distinct for distinct `p`, and have `p`'s arity. -/
structure WF (Ξ : RwSetting Voc) (φ : Formula Voc) (L : LNF Voc) : Prop where
  nodup : (L.lets.map LetDef.e).Nodup
  fresh_let : ∀ d ∈ L.lets, d.e ∉ Ξ.Cau ∧ d.e ∉ Ξ.Sup ∧ d.e ∉ Ξ.base ∧ d.e ∉ φ.preds
  fv_let : ∀ d ∈ L.lets, d.φ.fv = {x | x ∈ d.xs}
  arity_let : ∀ d ∈ L.lets, d.xs.length = Voc.ι d.e
  nodup_xs : ∀ d ∈ L.lets, d.xs.Nodup
  scope : ∀ k (hk : k < L.lets.length), ∀ e ∈ L.lets[k].φ.preds,
    ¬ IsLet L.lets e ∨ ∃ k' < k, ∃ hk' : k' < L.lets.length, L.lets[k'].e = e
  closed : ∀ χ ∈ L.chis, χ.fv = ∅
  clean : (∀ χ ∈ L.chis, χ.Clean ∅) ∧ ∀ d ∈ L.lets, d.φ.Clean {x | x ∈ d.xs}
  arity : (∀ d ∈ L.lets, d.φ.WellArity) ∧ ∀ χ ∈ L.chis, χ.WellArity
  obl_inj : ∀ p q, IsLet L.lets p → IsLet L.lets q →
    (Ξ.cauN p = Ξ.cauN q → p = q) ∧ (Ξ.supN p = Ξ.supN q → p = q) ∧ Ξ.cauN p ≠ Ξ.supN q
  obl_fresh : ∀ p, ∀ o ∈ ({Ξ.cauN p, Ξ.supN p} : Set Voc.ℰ), ¬ IsLet L.lets o ∧
    (∀ d ∈ L.lets, o ∉ d.φ.preds) ∧ ∀ χ ∈ L.chis, o ∉ χ.preds
  obl_arity : ∀ d ∈ L.lets, Voc.ι (Ξ.cauN d.e) = Voc.ι d.e ∧ Voc.ι (Ξ.supN d.e) = Voc.ι d.e
  agg_arity : ∀ d ∈ L.lets, ∀ ys ω ss gs ψ, d.φ = .agg ys ω ss gs ψ → ys.length = (Voc.ι' ω).2
  fun_ok : (∀ d ∈ L.lets, d.φ.FunOK) ∧ ∀ χ ∈ L.chis, χ.FunOK

/-- The events that may not occur in an input trace: let names and obligation
    names (Theorem 4.3). -/
def NewNames (Ξ : RwSetting Voc) (ℒ : List (LetDef Voc)) : Set Voc.ℰ :=
  {e | IsLet ℒ e} ∪ Set.range Ξ.cauN ∪ Set.range Ξ.supN

/-- No event of `σ` has a name in `N`. -/
def Admissible (N : Set Voc.ℰ) (σ : Trace Voc.toSignature) : Prop :=
  ∀ i, ∀ ev ∈ σ.D i, ev.e ∉ N

end Paper
