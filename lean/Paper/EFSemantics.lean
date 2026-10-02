/-
  §3.2 EF semantics (main.tex l.845–989, Algorithm 2).
-/
import Paper.EFSyntax
import Paper.Enforcer

namespace Paper

variable {Voc : Vocabulary}

/-! ## Interpretations and clauses (l.858–865) -/

/-- An element `p(ā)` of `ℰ × 𝔻*` (the elements of `C`, `S`, and `Ω`; l.854). -/
abbrev REv (Voc : Vocabulary) := Voc.ℰ × List Voc.𝔻

/-- An event as an element of `ℰ × 𝔻*`. -/
def Event.raw (ev : Event Voc.toSignature) : REv Voc := (ev.e, ev.args)

/-- An interpretation `R : ℰ ⇀ 𝒫(𝔻*)` (l.860).  Undefined is represented by
    `∅`: `R` is only used through membership `⟦t̄⟧_v ∈ R(p)` (NOTES.md, F1). -/
abbrev Interpretation (Voc : Vocabulary) := Voc.ℰ → Set (List Voc.𝔻)

/-- The domain of a partial valuation. -/
def Val.dom (v : Val Voc) : Set Voc.𝕍 := {x | (v x).isSome}

def GArg.eval (v : Val Voc) : GArg Voc → Option Voc.𝔻
  | .var x => v x
  | .val d => some d

def GArg.vars : GArg Voc → Set Voc.𝕍
  | .var x => {x}
  | .val _ => ∅

/-- The variables of a guard atom. -/
def Atom.vars : Atom Voc → Set Voc.𝕍
  | .pred _ args => {x | ∃ a ∈ args, x ∈ a.vars}
  | .eq x _ => {x}

/-- `⟦p(t̄)⟧_R = {v ∣ dom(v) = fv(t̄), ⟦t̄⟧_v ∈ R(p)}` and
    `⟦x == c⟧_R = {{x ↦ c}}` (l.862–863). -/
def Atom.sem (R : Interpretation Voc) : Atom Voc → Set (Val Voc)
  | .pred p args => {v | v.dom = (Atom.pred p args).vars ∧
      ∃ ds, args.mapM (GArg.eval v) = some ds ∧ ds ∈ R p}
  | .eq x c => {Val.empty.upd x c}

/-- Two partial valuations agree on their common domain. -/
def Val.Compat (v w : Val Voc) : Prop := ∀ x a b, v x = some a → w x = some b → a = b

/-- The union of two compatible partial valuations. -/
def Val.union (v w : Val Voc) : Val Voc := fun x => (v x).or (w x)

/-- `⋈`: the (natural) join of two sets of valuations. -/
def join (A B : Set (Val Voc)) : Set (Val Voc) :=
  {u | ∃ v ∈ A, ∃ w ∈ B, v.Compat w ∧ u = v.union w}

/-- `⋈_{γ ∈ κ} ⟦γ⟧_R` -/
def EGuard.sem (R : Interpretation Voc) (κ : EGuard Voc) : Set (Val Voc) :=
  κ.tail.foldl (fun A γ => join A (γ.sem R)) (κ.head.sem R)

/-- `v ⊨_R φ` for filters. -/
def Filter.holds (R : Interpretation Voc) (v : Val Voc) : Filter Voc → Prop
  | .tt => True
  | .ff => False
  | .pred p ts => ∃ ds, Term.evalList v ts = some ds ∧ ds ∈ R p
  | .and φ ψ => φ.holds R v ∧ ψ.holds R v
  | .or φ ψ => φ.holds R v ∨ ψ.holds R v
  | .not φ => ¬ φ.holds R v

def Filter.fv : Filter Voc → Set Voc.𝕍
  | .tt => ∅
  | .ff => ∅
  | .pred _ ts => Term.varsList ts
  | .and φ ψ => φ.fv ∪ ψ.fv
  | .or φ ψ => φ.fv ∪ ψ.fv
  | .not φ => φ.fv

/-- `⟦κ₁ or … or κ_m if φ⟧_R = {v ∈ ⋃ᵢ ⋈_{γ ∈ κᵢ} ⟦γ⟧_R ∣ v ⊨_R φ}` (l.864).
    A missing `if φ` is `if true`, and
    `⟦if φ⟧_R = {v ∣ dom(v) = fv(φ), v ⊨_R φ}`. -/
def Clause.sem (R : Interpretation Voc) : Clause Voc → Set (Val Voc)
  | .guarded π φ => {v | (∃ κ ∈ π.toList, v ∈ κ.sem R) ∧ ∀ f ∈ φ, f.holds R v}
  | .filter φ => {v | v.dom = φ.fv ∧ φ.holds R v}

/-- `v↾x̄ = (v(x₁), …, v(x_k))`, defined if `v` is defined on all `xᵢ` (l.877). -/
def Val.proj (v : Val Voc) (xs : List Voc.𝕍) : Option (List Voc.𝔻) := xs.mapM v

/-- `{v↾x̄ ∣ v ∈ ⟦c⟧_R}` -/
def rows (R : Interpretation Voc) (c : Clause Voc) (xs : List Voc.𝕍) : Set (List Voc.𝔻) :=
  {r | ∃ v ∈ c.sem R, v.proj xs = some r}

/-! ## States (l.852–855, 871–875) -/

/-- Tables: `T : ℰ ⇀ 𝒫(ℕ × 𝔻*)` holding timestamped rows `τ · r` (l.873–874). -/
abbrev Tables (Voc : Vocabulary) := Voc.ℰ → Set (ℕ × List Voc.𝔻)

/-- `{ts, tp}` -/
inductive DKind | ts | tp
  deriving DecidableEq

/-- An obligation `(e, ā, (k, n)) ∈ ℰ × 𝔻* × ({ts, tp} × ℕ)` (l.854). -/
abbrev Obligation (Voc : Vocabulary) := REv Voc × (DKind × ℕ)

/-- The enforcer state `(T, T^○, Ω)` (l.852). -/
structure EState (Voc : Vocabulary) where
  T : Tables Voc
  TN : Tables Voc
  Ω : Set (Obligation Voc)

/-- The working set `𝒮 = (T, τ, D, C, S)` (l.871). -/
structure WorkingSet (Voc : Vocabulary) where
  T : Tables Voc
  τ : ℕ
  D : Set (REv Voc)
  C : Set (REv Voc)
  S : Set (REv Voc)

/-- `\overline{s}^I = {ā ∣ τ' · ā ∈ s, τ − τ' ∈ I}` for `I = [n, b]` (l.875),
    as used by `Eval` (`\overline{T(p)}^{[n,b]}`). -/
def window (s : Set (ℕ × List Voc.𝔻)) (τ n : ℕ) (b : ℕ∞) : Set (List Voc.𝔻) :=
  {a | ∃ τ', (τ', a) ∈ s ∧ τ' ≤ τ ∧ n ≤ τ - τ' ∧ ((τ - τ' : ℕ) : ℕ∞) ≤ b}

/-! ## Program structure -/

namespace Item

/-- The name `pᵢ` defined by a definition `dᵢ`. -/
def defName? : Item Voc → Option Voc.ℰ
  | .table _ _ p _ _ _ _ => some p
  | .let_ _ _ p _ _ => some p
  | .agg _ p _ _ _ _ _ => some p
  | _ => none

def isRule : Item Voc → Bool
  | .rule .. => true
  | _ => false

end Item

/-- The definitions `d₁, …, dₙ` of `P` (its `table`, `let` and `agg` items, in
    order) and the names `p₁, …, pₙ` they define. -/
def Program.defs (P : Program Voc) : List (Voc.ℰ × Item Voc) :=
  P.items.filterMap fun d => d.defName?.map (·, d)

/-- Group the rules by sections: a `section` declaration groups all following
    rules until the next `section` (l.763–765).  Every rule must belong to a
    section; rules before the first `section` are not evaluated. -/
def sectionsAux : List (Item Voc) → Option (SecKind × List (Item Voc)) →
    List (SecKind × List (Item Voc))
  | [], none => []
  | [], some g => [g]
  | .sec k :: r, none => sectionsAux r (some (k, []))
  | .sec k :: r, some g => g :: sectionsAux r (some (k, []))
  | it :: r, cur =>
    if it.isRule then sectionsAux r (cur.map fun g => (g.1, g.2 ++ [it])) else sectionsAux r cur

def Program.sections (P : Program Voc) : List (SecKind × List (Item Voc)) :=
  sectionsAux P.items none

/-! ## Algorithm 2 -/

section Alg2
open Classical
variable (P : Program Voc)

/-- `Eval(d, R, T, τ)` (l.955–970).  A missing `[window n b]` is `[window 0 *]`
    and a missing `remove` clause removes nothing (NOTES.md, N5). -/
def Eval (d : Item Voc) (R : Interpretation Voc) (T : Tables Voc) (τ : ℕ) : Set (List Voc.𝔻) :=
  match d with
  -- `let p(x̄) := {c}`: `{v↾x̄ ∣ v ∈ ⟦c⟧_R}`
  | .let_ _ _ _ cols c => rows R c (cols.map Col.name)
  -- `table p(x̄) [window n b] := add {a} remove {r}`:
  -- `(\overline{T(p)}^{[n,b]} ∖ {v↾x̄ ∣ v ∈ ⟦r⟧_R}) ∪ (n = 0 ? {v↾x̄ ∣ v ∈ ⟦a⟧_R} : ∅)`
  | .table _ false p cols w a r =>
    let (n, b) := w.getD (0, ⊤)
    (window (T p) τ n b \ (match r with | some r => rows R r (cols.map Col.name) | none => ∅)) ∪
      (if n = 0 then rows R a (cols.map Col.name) else ∅)
  -- `lagged table p(x̄) [window n b] := add {c}`: `\overline{T(p)}^{[n,b]}`
  | .table _ true p _ w _ _ =>
    let (n, b) := w.getD (0, ⊤)
    window (T p) τ n b
  -- `agg let p(ḡ, ō) := g(s̄) group_by ḡ over {c}`:
  -- `{v̄(ḡ) · w̄ ∣ v̄ ∈ ⟦c⟧_R, w̄ ∈ ĝ⟅⟦s̄⟧_v ∣ v ∈ ⟦c⟧_R, v(ḡ) = v̄(ḡ)⟆}`.
  -- `ĝ` is applied only to finite multisets (NOTES.md, F4).
  | .agg _ _ _ g ss gs c =>
    {row | ∃ vb ∈ c.sem R, ∃ gv, vb.proj gs = some gv ∧
      let grp := {v | v ∈ c.sem R ∧ gs.map v = gs.map vb}
      ∃ hfin : grp.Finite, ∃ M : Multiset (Fin (Voc.ι' g).1 → Voc.𝔻),
        M.map some = hfin.toFinset.val.map (fun v => (Term.evalList v ss).bind (toVec _)) ∧
        ∃ w ∈ Voc.ωhat g M, row = gv ++ List.ofFn w}
  | _ => ∅

/-- `Interp(𝒮)`: `R₀ ← (D ∖ S) ∪ C`, then
    `Rᵢ ← R_{i−1}[pᵢ ↦ Eval(dᵢ, R_{i−1}, T, τ)]` for `i = 1, …, n`. -/
def Interp (𝒮 : WorkingSet Voc) : Interpretation Voc :=
  let R₀ : Interpretation Voc := fun p => {r | (p, r) ∈ (𝒮.D \ 𝒮.S) ∪ 𝒮.C}
  P.defs.foldl (fun R d => Function.update R d.1 (Eval d.2 R 𝒮.T 𝒮.τ)) R₀

/-- `|σ|` as a natural number; Algorithm 1 only calls `μ` and `ν` on finite
    `σ` (NOTES.md, F3). -/
def Trace.len {Sig : Signature} (σ : Trace Sig) : ℕ := σ.length.toNat

/-- `Update(r, Ω, 𝒮, σ)` (l.972–986). -/
def Update (r : Item Voc) (Ω : Set (Obligation Voc)) (𝒮 : WorkingSet Voc)
    (σ : Trace Voc.toSignature) : Set (Obligation Voc) × Set (REv Voc) × Set (REv Voc) :=
  match r with
  | .rule _ α p ts delay next c =>
    -- `A ← {⟦t̄⟧_v ∣ v ∈ ⟦c⟧_{Interp(𝒮)}}`
    let A : Set (List Voc.𝔻) := {a | ∃ v ∈ c.sem (Interp P 𝒮), Term.evalList v ts = some a}
    match delay, next, α with
    | some N, _, _ => (Ω ∪ {o | ∃ a ∈ A, o = ((p, a), (.ts, 𝒮.τ + N))}, 𝒮.C, 𝒮.S)
    | none, some N, _ => (Ω ∪ {o | ∃ a ∈ A, o = ((p, a), (.tp, Trace.len σ + N))}, 𝒮.C, 𝒮.S)
    | none, none, .plus => (Ω, 𝒮.C ∪ {e | ∃ a ∈ A, e = (p, a)}, 𝒮.S)
    | none, none, .minus => (Ω, 𝒮.C, 𝒮.S ∪ {e | ∃ a ∈ A, e = (p, a)})
  | _ => (Ω, 𝒮.C, 𝒮.S)

/-- `repeat body until x unchanged`: runs `body` at least once and stops after
    the first pass that leaves the state unchanged; `none` if it never stops.
    This is the loop as a partial function. -/
noncomputable def repeatUntilUnchanged {α : Type} (body : α → α) (x : α) : Option α :=
  open Classical in
  if h : ∃ k, body^[k + 1] x = body^[k] x then some (body^[Nat.find h + 1] x) else none

/-- `for all rule r ∈ s: (Ω, C, S) ← Update(r, Ω, 𝒮, σ)` (l.923–925), where
    `𝒮 = (T, τ, D, C, S)` carries the current `C` and `S`. -/
def pass (rs : List (Item Voc)) (T : Tables Voc) (τ : ℕ) (D : Set (REv Voc))
    (σ : Trace Voc.toSignature) :
    Set (Obligation Voc) × Set (REv Voc) × Set (REv Voc) →
    Set (Obligation Voc) × Set (REv Voc) × Set (REv Voc) :=
  fun x => rs.foldl (fun (Ω, C, S) r => Update P r Ω ⟨T, τ, D, C, S⟩ σ) x

/-- `repeat … until (Ω, C, S) unchanged or s is once` (l.922–926). -/
noncomputable def runSection (s : SecKind × List (Item Voc)) (T : Tables Voc) (τ : ℕ)
    (D : Set (REv Voc)) (σ : Trace Voc.toSignature)
    (x : Set (Obligation Voc) × Set (REv Voc) × Set (REv Voc)) :
    Option (Set (Obligation Voc) × Set (REv Voc) × Set (REv Voc)) :=
  match s.1 with
  | .once => some (pass P s.2 T τ D σ x)
  | .fixpoint => repeatUntilUnchanged (pass P s.2 T τ D σ) x

/-- `for all section s of P in order` (l.921). -/
noncomputable def runSections : List (SecKind × List (Item Voc)) → Tables Voc → ℕ →
    Set (REv Voc) → Trace Voc.toSignature →
    Set (Obligation Voc) × Set (REv Voc) × Set (REv Voc) →
    Option (Set (Obligation Voc) × Set (REv Voc) × Set (REv Voc))
  | [], _, _, _, _, x => some x
  | s :: ss, T, τ, D, σ, x =>
    (runSection P s T τ D σ x).bind (runSections ss T τ D σ)

/-- The table updates (l.928–932): for each `table pᵢ(x̄ᵢ) := add {aᵢ} remove {rᵢ}`
    in order, `T(pᵢ) ← (T(pᵢ) ∖ {τ'·v↾x̄ᵢ ∣ v ∈ ⟦rᵢ⟧_{Interp(𝒮)}, τ' ∈ ℕ})
    ∪ {τ·v↾x̄ᵢ ∣ v ∈ ⟦aᵢ⟧_{Interp(𝒮)}}`.  `𝒮` refers to the current `T`: each
    `Interp(𝒮)` sees the tables updated before it. -/
def updTable (τ : ℕ) (D C S : Set (REv Voc)) (T : Tables Voc) : Item Voc → Tables Voc
  | .table _ false p cols _ a r =>
    let R := Interp P ⟨T, τ, D, C, S⟩
    let xs := cols.map Col.name
    Function.update T p
      ((T p \ {tr | ∃ rr, (match r with | some r => rr ∈ rows R r xs | none => False) ∧
          tr.2 = rr}) ∪
        {tr | tr.1 = τ ∧ tr.2 ∈ rows R a xs})
  | _ => T

/-- The lagged-table updates (l.933–940): first `T^○(pᵢ) ← {τ·v↾x̄ᵢ ∣ v ∈
    ⟦cᵢ⟧_{Interp(𝒮)}}` for each `lagged table pᵢ(x̄ᵢ) := add {cᵢ}`, then
    `T(pᵢ) ← T^○(pᵢ)` for each of them.  The first loop does not change `T`,
    so every `Interp(𝒮)` is taken with the tables `T` of the start of the
    first loop, and the two loops are merged into one fold. -/
def updLagged (τ : ℕ) (D C S : Set (REv Voc)) (T : Tables Voc) (TT : Tables Voc × Tables Voc) :
    Item Voc → Tables Voc × Tables Voc
  | .table _ true p cols _ c _ =>
    let R := Interp P ⟨T, τ, D, C, S⟩
    let TN := Function.update TT.2 p {tr | tr.1 = τ ∧ tr.2 ∈ rows R c (cols.map Col.name)}
    (Function.update TT.1 p (TN p), TN)
  | _ => TT

/-- `Saturate(𝒮 = (T, τ, D, C, S), T^○, Ω, σ)` (l.920–940), returning
    `(T, C, S, Ω)`; `none` if a `fixpoint` section does not terminate. -/
noncomputable def Saturate (𝒮 : WorkingSet Voc) (TN : Tables Voc) (Ω : Set (Obligation Voc))
    (σ : Trace Voc.toSignature) :
    Option (Tables Voc × Set (REv Voc) × Set (REv Voc) × Set (Obligation Voc)) :=
  (runSections P P.sections 𝒮.T 𝒮.τ 𝒮.D σ (Ω, 𝒮.C, 𝒮.S)).map fun (Ω, C, S) =>
    let T := P.items.foldl (updTable P 𝒮.τ 𝒮.D C S) 𝒮.T
    let T := (P.items.foldl (updLagged P 𝒮.τ 𝒮.D C S T) (T, TN)).1
    (T, C, S, Ω)

/-- `μ((T, T^○, Ω), σ, τ, D)`, returning `((T, T^○, Ω), C, S)`. -/
noncomputable def mu (st : EState Voc) (σ : Trace Voc.toSignature) (τ : ℕ) (D : Set (REv Voc)) :
    Option (EState Voc × Set (REv Voc) × Set (REv Voc)) :=
  let O := {e | (e, (DKind.tp, Trace.len σ)) ∈ st.Ω}
  (Saturate P ⟨st.T, τ, D, O, ∅⟩ st.TN st.Ω σ).map fun (T, C, S, Ω) =>
    (⟨T, st.TN, Ω⟩, C, S)

/-- `ν((T, T^○, Ω), σ, τ)` (l.911–918). -/
noncomputable def nu (st : EState Voc) (σ : Trace Voc.toSignature) (τ : ℕ) :
    Option (EState Voc × Option (Set (REv Voc))) :=
  let C := {e | (e, (DKind.tp, Trace.len σ)) ∈ st.Ω ∨ (e, (DKind.ts, τ)) ∈ st.Ω}
  open Classical in
  if C = ∅ then some (st, none)
  else (Saturate P ⟨st.T, τ, ∅, C, ∅⟩ st.TN st.Ω σ).map fun (T, C, _S, Ω) =>
    (⟨T, st.TN, Ω⟩, some C)

end Alg2

end Paper
