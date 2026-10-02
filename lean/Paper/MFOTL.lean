/-
  §2.2 Metric first-order temporal logic (main.tex l.517–628, Figure 1).
-/
import Paper.Traces

namespace Paper

/-- The fixed vocabulary of MFOTL (l.530–538): variables `𝕍`, function symbols
    `𝔽` with arity `ι` and interpretation `f̂ : 𝔻^{ι(f)} → 𝔻`, aggregation
    operator symbols `Ω` with arity `ι' : Ω → ℕ²` and interpretation `ω̂` mapping
    finite multisets over `𝔻ⁿ` to finite subsets of `𝔻ᵐ`, where `ι'(ω) = (n, m)`. -/
structure Vocabulary extends Signature where
  𝕍 : Type
  [decV : DecidableEq 𝕍]
  𝔽 : Type
  ιF : 𝔽 → ℕ
  fhat : (f : 𝔽) → (Fin (ιF f) → 𝔻) → 𝔻
  Ω : Type
  ι' : Ω → ℕ × ℕ
  ωhat : (ω : Ω) → Multiset (Fin (ι' ω).1 → 𝔻) → Finset (Fin (ι' ω).2 → 𝔻)

attribute [instance] Vocabulary.decV

variable {Voc : Vocabulary}

/-! ## Intervals -/

/-- `𝕀`: the non-empty intervals of `ℕ` (l.545). -/
def Interval : Type := {I : Set ℕ // I.Nonempty ∧ I.OrdConnected}

instance : Membership ℕ Interval := ⟨fun I n => n ∈ I.1⟩

namespace Interval

/-- `[a, b]` for `a ≤ b ∈ ℕ ∪ {∞}`. -/
def icc (a : ℕ) (b : ℕ∞) (h : (a : ℕ∞) ≤ b) : Interval :=
  ⟨{n | a ≤ n ∧ (n : ℕ∞) ≤ b}, ⟨a, le_rfl, h⟩, ⟨by
    intro x hx y hy z hz
    exact ⟨hx.1.trans hz.1, (Nat.cast_le.2 hz.2).trans hy.2⟩⟩⟩

/-- `[0, ∞)`, omitted from subscripts (l.558). -/
def univ : Interval := icc 0 ⊤ le_top

end Interval

/-! ## Terms -/

/-- Valuations `v : 𝕍 ⇀ 𝔻` (l.619). -/
abbrev Val (Voc : Vocabulary) := Voc.𝕍 → Option Voc.𝔻

/-- `v[x ↦ d]`. -/
def Val.upd (v : Val Voc) (x : Voc.𝕍) (d : Voc.𝔻) : Val Voc := Function.update v x (some d)

/-- The empty valuation `∅`. -/
def Val.empty : Val Voc := fun _ => none

/-- Terms `t ::= x ∣ c ∣ f(t̄)` (l.540). -/
inductive Term (Voc : Vocabulary) where
  | var : Voc.𝕍 → Term Voc
  | const : Voc.𝔻 → Term Voc
  | app : Voc.𝔽 → List (Term Voc) → Term Voc

/-- Read a list of exactly `n` values as a tuple in `𝔻ⁿ`. -/
def toVec {α : Type} (n : ℕ) (l : List α) : Option (Fin n → α) :=
  if h : l.length = n then some (fun i => l[i.1]'(h ▸ i.2)) else none

mutual
/-- `⟦t⟧_v` (l.620–621): `⟦x⟧_v = v(x)`, `⟦c⟧_v = c`, `⟦f(t̄)⟧_v = f̂(⟦t̄⟧_v)`.
    Undefined (`none`) if `v` is undefined on a variable of `t`, or if `f` is
    applied to a wrong number of arguments. -/
def Term.eval (v : Val Voc) : Term Voc → Option Voc.𝔻
  | .var x => v x
  | .const c => some c
  | .app f ts => do
      let ds ← Term.evalList v ts
      let a ← toVec (Voc.ιF f) ds
      pure (Voc.fhat f a)
/-- `⟦t̄⟧_v`. -/
def Term.evalList (v : Val Voc) : List (Term Voc) → Option (List Voc.𝔻)
  | [] => some []
  | t :: ts => do
      let d ← Term.eval v t
      let ds ← Term.evalList v ts
      pure (d :: ds)
end

mutual
/-- Variables of a term. -/
def Term.vars : Term Voc → Set Voc.𝕍
  | .var x => {x}
  | .const _ => ∅
  | .app _ ts => Term.varsList ts
def Term.varsList : List (Term Voc) → Set Voc.𝕍
  | [] => ∅
  | t :: ts => Term.vars t ∪ Term.varsList ts
end

mutual
/-- `t[d/x]`. -/
def Term.subst (d : Voc.𝔻) (x : Voc.𝕍) : Term Voc → Term Voc
  | .var y => if y = x then .const d else .var y
  | .const c => .const c
  | .app f ts => .app f (Term.substList d x ts)
def Term.substList (d : Voc.𝔻) (x : Voc.𝕍) : List (Term Voc) → List (Term Voc)
  | [] => []
  | t :: ts => Term.subst d x t :: Term.substList d x ts
end

/-! ## Formulas -/

/-- MFOTL formulas (l.541):
    `φ ::= ⊤ ∣ e(t̄) ∣ x = c ∣ ¬φ ∣ φ ∧ φ ∣ ∃x. φ ∣ ○_I φ ∣ ●_I φ ∣ ◇_I φ ∣ φ S_I φ
         ∣ let e(x̄) = φ in φ ∣ ȳ ← ω(t̄; ḡ) φ`.

    In `agg ys ω ss gs φ`, `ys` are the result variables, `ss` the aggregated
    terms and `gs` the group-by variables; `eq x c` is the equality `x = c`. -/
inductive Formula (Voc : Vocabulary) where
  | top : Formula Voc
  | pred : Voc.ℰ → List (Term Voc) → Formula Voc
  | neg : Formula Voc → Formula Voc
  | and : Formula Voc → Formula Voc → Formula Voc
  | ex : Voc.𝕍 → Formula Voc → Formula Voc
  | next : Interval → Formula Voc → Formula Voc
  | prev : Interval → Formula Voc → Formula Voc
  | eventually : Interval → Formula Voc → Formula Voc
  | since : Interval → Formula Voc → Formula Voc → Formula Voc
  | letin : Voc.ℰ → List Voc.𝕍 → Formula Voc → Formula Voc → Formula Voc
  | agg : List Voc.𝕍 → Voc.Ω → List (Term Voc) → List Voc.𝕍 → Formula Voc → Formula Voc
  | eq : Voc.𝕍 → Voc.𝔻 → Formula Voc

namespace Formula

/-- The formulas of the grammar of l.541. -/
def IsMFOTL : Formula Voc → Prop
  | top => True
  | pred _ _ => True
  | neg φ => φ.IsMFOTL
  | and φ ψ => φ.IsMFOTL ∧ ψ.IsMFOTL
  | ex _ φ => φ.IsMFOTL
  | next _ φ => φ.IsMFOTL
  | prev _ φ => φ.IsMFOTL
  | eventually _ φ => φ.IsMFOTL
  | since _ φ ψ => φ.IsMFOTL ∧ ψ.IsMFOTL
  | letin _ _ φ ψ => φ.IsMFOTL ∧ ψ.IsMFOTL
  | agg _ _ _ _ φ => φ.IsMFOTL
  | eq _ _ => True

/-! ### Abbreviations (l.546–558) -/

/-- `⊥ ≔ ¬⊤` -/
def bot : Formula Voc := neg top
/-- `φ ∨ ψ ≔ ¬(¬φ ∧ ¬ψ)` -/
def or (φ ψ : Formula Voc) : Formula Voc := neg (and (neg φ) (neg ψ))
/-- `φ → ψ ≔ ¬φ ∨ ψ` -/
def imp (φ ψ : Formula Voc) : Formula Voc := or (neg φ) ψ
/-- `φ ↔ ψ ≔ (φ → ψ) ∧ (ψ → φ)` -/
def iff (φ ψ : Formula Voc) : Formula Voc := and (imp φ ψ) (imp ψ φ)
/-- `∀x. φ ≔ ¬(∃x. ¬φ)` -/
def all (x : Voc.𝕍) (φ : Formula Voc) : Formula Voc := neg (ex x (neg φ))
/-- `⧫_I φ ≔ ⊤ S_I φ` -/
def once (I : Interval) (φ : Formula Voc) : Formula Voc := since I top φ
/-- `□_I φ ≔ ¬◇_I ¬φ` -/
def always (I : Interval) (φ : Formula Voc) : Formula Voc := neg (eventually I (neg φ))
/-- `□ φ` (the `[0, ∞)` subscript omitted). -/
def Always (φ : Formula Voc) : Formula Voc := always Interval.univ φ

/-- `fv(φ)` (l.585).  Following the caption of Figure 1, the free variables of
    `ȳ ← ω(s̄; ḡ) φ` are `ḡ ∪ ȳ`.  The free variables of `let e(x̄) = φ in ψ` are
    those of `ψ`: by Figure 1, `φ` is evaluated under valuations `v'`
    independent of `v` (NOTES.md, N3). -/
def fv : Formula Voc → Set Voc.𝕍
  | top => ∅
  | pred _ ts => Term.varsList ts
  | neg φ => fv φ
  | and φ ψ => fv φ ∪ fv ψ
  | ex x φ => fv φ \ {x}
  | next _ φ => fv φ
  | prev _ φ => fv φ
  | eventually _ φ => fv φ
  | since _ φ ψ => fv φ ∪ fv ψ
  | letin _ _ _ ψ => fv ψ
  | agg ys _ _ gs _ => {x | x ∈ gs} ∪ {x | x ∈ ys}
  | eq x _ => {x}

/-- `φ[d/x]`: substitute the constant `d` for the free variable `x` (l.559).
    Undefined (`none`) on an aggregation with `x ∈ ḡ ∪ ȳ`: there `x` is free
    but occurs only in variable positions, where a constant cannot be
    substituted (NOTES.md, N2). -/
def subst (d : Voc.𝔻) (x : Voc.𝕍) : Formula Voc → Option (Formula Voc)
  | top => some top
  | pred e ts => some (pred e (Term.substList d x ts))
  | neg φ => neg <$> subst d x φ
  | and φ ψ => and <$> subst d x φ <*> subst d x ψ
  | ex y φ => if y = x then some (ex y φ) else ex y <$> subst d x φ
  | next I φ => next I <$> subst d x φ
  | prev I φ => prev I <$> subst d x φ
  | eventually I φ => eventually I <$> subst d x φ
  | since I φ ψ => since I <$> subst d x φ <*> subst d x ψ
  | letin e xs φ ψ => letin e xs φ <$> subst d x ψ
  | agg ys ω ss gs φ => if x ∈ ys ∨ x ∈ gs then none else some (agg ys ω ss gs φ)
  | eq y c => if y = x then none else some (eq y c)

end Formula

/-! ## Semantics (Figure 1) -/

/-- The structure a formula is evaluated on: Figure 1 fixes an *infinite*
    trace `σ` (caption, l.610).  `σ[e ↦ φ]` may have infinite databases, so the
    semantics is defined on infinite sequences of timestamps and (possibly
    infinite) databases; `Trace.toStr` embeds the infinite traces. -/
structure Str (Sig : Signature) where
  τ : ℕ → ℕ
  D : ℕ → DB Sig

/-- An infinite trace as a `Str`. -/
def Trace.toStr {Sig : Signature} (σ : Trace Sig) : Str Sig := ⟨σ.τ, σ.D⟩

/-- `v` is defined on all of `X` (Figure 1 is given for valuations "whose
    domain includes" the free variables, l.619). -/
def Val.Covers (v : Val Voc) (X : Set Voc.𝕍) : Prop := ∀ x ∈ X, (v x).isSome

/-- `σ[e ↦ φ]` (Figure 1 caption, l.612–613): extends each `D_j` with
    `{e(⟦x̄⟧_{v'}) ∣ v', j ⊨_σ φ}`.  `sat` stands for `v', j ⊨_σ φ` and `fvφ` for
    `fv(φ)`: as everywhere in Figure 1, `v'` ranges over the valuations whose
    domain includes `fv(φ)`. -/
def Str.extend (σ : Str Voc.toSignature) (e : Voc.ℰ) (xs : List Voc.𝕍) (fvφ : Set Voc.𝕍)
    (sat : Val Voc → ℕ → Prop) : Str Voc.toSignature where
  τ := σ.τ
  D := fun j => σ.D j ∪
    {ev | ev.e = e ∧ ∃ v' : Val Voc, v'.Covers fvφ ∧ xs.map v' = ev.args.map some ∧ sat v' j}

/-- `v, i ⊨_σ φ` (Figure 1). -/
def Formula.sat : Formula Voc → Str Voc.toSignature → Val Voc → ℕ → Prop
  | .top, _, _, _ => True
  -- `(e, ⟦t̄⟧_v) ∈ Dᵢ`
  | .pred e ts, σ, v, i =>
      ∃ ds, Term.evalList v ts = some ds ∧ ∃ ev ∈ σ.D i, ev.e = e ∧ ev.args = ds
  | .neg φ, σ, v, i => ¬ φ.sat σ v i
  | .and φ ψ, σ, v, i => φ.sat σ v i ∧ ψ.sat σ v i
  | .ex x φ, σ, v, i => ∃ d, φ.sat σ (v.upd x d) i
  | .next I φ, σ, v, i => φ.sat σ v (i + 1) ∧ σ.τ (i + 1) - σ.τ i ∈ I
  | .prev I φ, σ, v, i => i > 0 ∧ φ.sat σ v (i - 1) ∧ σ.τ i - σ.τ (i - 1) ∈ I
  | .eventually I φ, σ, v, i => ∃ j ≥ i, σ.τ j - σ.τ i ∈ I ∧ φ.sat σ v j
  | .since I φ ψ, σ, v, i =>
      ∃ j ≤ i, σ.τ i - σ.τ j ∈ I ∧ ψ.sat σ v j ∧ ∀ k, j < k → k ≤ i → φ.sat σ v k
  | .letin e xs φ ψ, σ, v, i => ψ.sat (σ.extend e xs φ.fv (fun v' j => φ.sat σ v' j)) v i
  -- `v(ȳ) ∈ ω̂⟅⟦s̄⟧_{v'} ∣ v' ∈ 𝒢⟆` and `𝒢` is finite and non-empty, where
  -- `𝒢 = {v' ∣ dom(v') = fv(φ), v'(ḡ) = v(ḡ), v', i ⊨ φ}`.
  | .agg ys ω ss gs φ, σ, v, i =>
      let 𝒢 := {v' : Val Voc | (∀ x, (v' x).isSome ↔ x ∈ φ.fv) ∧
                  gs.map v' = gs.map v ∧ φ.sat σ v' i}
      𝒢.Nonempty ∧ ∃ h𝒢 : 𝒢.Finite, ∃ M : Multiset (Fin (Voc.ι' ω).1 → Voc.𝔻),
        M.map some = h𝒢.toFinset.val.map (fun v' => (Term.evalList v' ss).bind (toVec _)) ∧
        ∃ y, ((ys.map v).mapM id).bind (toVec _) = some y ∧ y ∈ Voc.ωhat ω M
  -- `v, i ⊨ x = c` iff `v(x) = c`
  | .eq x c, _, v, _ => v x = some c

/-- `v, i ⊨_σ φ` for a trace `σ`.  Figure 1 defines it for infinite `σ` only. -/
def Formula.satTr (φ : Formula Voc) (σ : Trace Voc.toSignature) (v : Val Voc) (i : ℕ) : Prop :=
  σ.length = ⊤ ∧ φ.sat σ.toStr v i

end Paper
