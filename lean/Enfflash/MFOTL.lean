/-
  Enfflash formalization — MFOTL: syntax and semantics (paper, Section 2.2),
  and the let-normal form of MFOTL formulas that the compiler works on
  (Section 4.1).

  Variables are de Bruijn indices; a valuation is a function `ℕ → D`.
  Function applications are *semantic*: `Term.fn f` evaluates to `f v`.  This
  makes substitution lemmas trivial while keeping variables and constants
  syntactic (which is all that guards and data-flow analyses inspect).

  Predicates are either events (base events or the obligation events
  `Cau_p` / `Sup_p` introduced by the compiler) or let-bound predicates.
-/
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Set.Card

namespace Enfflash

universe u

/-! ## Valuations -/

/-- Prepend a value to a valuation (the semantics of a binder). -/
def vcons {D : Type u} (d : D) (v : ℕ → D) : ℕ → D
  | 0 => d
  | n + 1 => v n

/-- Prepend a list of values to a valuation. -/
def vapp {D : Type u} : List D → (ℕ → D) → ℕ → D
  | [], v => v
  | d :: ds, v => vcons d (vapp ds v)

@[simp] theorem vcons_zero {D : Type u} (d : D) (v : ℕ → D) : vcons d v 0 = d := rfl
@[simp] theorem vcons_succ {D : Type u} (d : D) (v : ℕ → D) (n : ℕ) :
    vcons d v (n + 1) = v n := rfl
@[simp] theorem vapp_nil {D : Type u} (v : ℕ → D) : vapp [] v = v := rfl
@[simp] theorem vapp_cons {D : Type u} (d : D) (ds : List D) (v : ℕ → D) :
    vapp (d :: ds) v = vcons d (vapp ds v) := rfl

theorem vapp_lt {D : Type u} (ds : List D) (v : ℕ → D) (n : ℕ) (h : n < ds.length) :
    vapp ds v n = ds[n] := by
  induction ds generalizing n with
  | nil => simp at h
  | cons d ds ih =>
    cases n with
    | zero => rfl
    | succ n => simp [vapp, vcons]; exact ih n (by simpa using h)

theorem vapp_ge {D : Type u} (ds : List D) (v : ℕ → D) (n : ℕ) :
    vapp ds v (n + ds.length) = v n := by
  induction ds generalizing n with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.length_cons, vapp_cons]
    rw [show n + (ds.length + 1) = (n + ds.length) + 1 by omega]
    simp [ih]

theorem vapp_append {D : Type u} (ds es : List D) (v : ℕ → D) :
    vapp (ds ++ es) v = vapp ds (vapp es v) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [ih]

/-! ## Terms -/

/-- Terms.  A function application `fn f xs` is represented semantically by
    the function `f` of the valuation, together with its *support* `xs`, the
    variables it reads (see `Term.WF`). -/
inductive Term (D : Type u) where
  | var : ℕ → Term D
  | const : D → Term D
  | fn : ((ℕ → D) → D) → List ℕ → Term D

namespace Term
variable {D : Type u}

def eval (v : ℕ → D) : Term D → D
  | var n => v n
  | const d => d
  | fn f _ => f v

/-- The variables a term reads. -/
def supp : Term D → List ℕ
  | var n => [n]
  | const _ => []
  | fn _ xs => xs

/-- Well-formedness: a function term only reads its support. -/
def WF : Term D → Prop
  | fn f xs => ∀ v v' : ℕ → D, (∀ n ∈ xs, v n = v' n) → f v = f v'
  | _ => True

/-- Parallel substitution of terms for variables. -/
def subst (s : ℕ → Term D) : Term D → Term D
  | var n => s n
  | const d => const d
  | fn f xs => fn (fun w => f (fun n => (s n).eval w)) (xs.flatMap fun n => (s n).supp)

@[simp] theorem eval_subst (s : ℕ → Term D) (v : ℕ → D) (t : Term D) :
    (t.subst s).eval v = t.eval (fun n => (s n).eval v) := by
  cases t <;> rfl

theorem eval_congr (t : Term D) (ht : t.WF) (v v' : ℕ → D) (h : ∀ n ∈ t.supp, v n = v' n) :
    t.eval v = t.eval v' := by
  cases t with
  | var n => exact h n (by simp [supp])
  | const => rfl
  | fn f xs => exact ht v v' h

/-- The variables occurring syntactically (function terms are opaque). -/
def isVar (x : ℕ) : Term D → Prop
  | var n => n = x
  | _ => False

/-- A term is *stable* if it cannot create new domain values. -/
def stable : Term D → Prop
  | fn _ _ => False
  | _ => True

end Term

/-- Shift all variables up by `k` (used when a formula is placed under `k`
    fresh local variables). -/
def liftS {D : Type u} (k : ℕ) : ℕ → Term D := fun n => .var (n + k)

/-- Lift a substitution under one binder. -/
def upS {D : Type u} (s : ℕ → Term D) : ℕ → Term D
  | 0 => .var 0
  | n + 1 => (s n).subst (liftS 1)

theorem eval_upS {D : Type u} (s : ℕ → Term D) (d : D) (v : ℕ → D) :
    (fun n => (upS s n).eval (vcons d v)) = vcons d (fun n => (s n).eval v) := by
  funext n; cases n with
  | zero => rfl
  | succ n =>
    show (Term.subst (liftS 1) (s n)).eval (vcons d v) = (s n).eval v
    rw [Term.eval_subst]; congr

/-- Substitution that keeps the first `k` variables and instantiates the
    `k`-th one with a constant (shifting the remaining ones down). -/
def instS {D : Type u} (k : ℕ) (d : D) : ℕ → Term D := fun n =>
  if n < k then .var n else if n = k then .const d else .var (n - 1)

theorem eval_instS {D : Type u} (ds : List D) (d : D) (v : ℕ → D) :
    (fun n => (instS ds.length d n).eval (vapp ds v)) = vapp ds (vcons d v) := by
  funext n
  simp only [instS]
  split_ifs with h1 h2
  · simp [Term.eval, vapp_lt _ _ _ h1]
  · subst h2; simpa [Term.eval] using (vapp_ge ds (vcons d v) 0).symm
  · obtain ⟨m, rfl⟩ : ∃ m, n = (m + 1) + ds.length := ⟨n - ds.length - 1, by omega⟩
    simp only [Term.eval]
    rw [show m + 1 + ds.length - 1 = m + ds.length by omega, vapp_ge, vapp_ge]; rfl

theorem eval_liftS {D : Type u} (ds : List D) (v : ℕ → D) :
    (fun n => (liftS ds.length n : Term D).eval (vapp ds v)) = v := by
  funext n; simp [liftS, Term.eval, vapp_ge]

/-- `upS` iterated `k` times: a substitution under `k` binders. -/
def upSn {D : Type u} : ℕ → (ℕ → Term D) → ℕ → Term D
  | 0, s => s
  | k + 1, s => upS (upSn k s)

theorem eval_upSn {D : Type u} (s : ℕ → Term D) (v : ℕ → D) :
    ∀ ds : List D,
      (fun n => (upSn ds.length s n).eval (vapp ds v)) = vapp ds (fun n => (s n).eval v)
  | [] => rfl
  | d :: ds => by
    show (fun n => (upS (upSn ds.length s) n).eval (vcons d (vapp ds v))) = _
    rw [eval_upS, eval_upSn s v ds]; rfl

/-! ## Aggregation operators -/

/-- An aggregation operator `ω` (e.g. `SUM`, `CNT`, or a user-defined
    `tfun`): it maps a multiset of rows, given by the multiplicity of each
    row, to a set of result rows; finite multisets yield finitely many
    results. -/
structure AggOp (D : Type u) where
  op : (List D → ℕ∞) → List D → Prop
  fin : ∀ M : List D → ℕ∞, {r | M r ≠ 0}.Finite → (∀ r, M r ≠ ⊤) →
    {r | op M r}.Finite

/-- The multiset `⟅t̄⟧_{v'} | v' ∈ 𝒢⟆` of an aggregation: the multiplicity
    of row `r` is the number of valuations `ds` of the `k` aggregated
    variables satisfying `P` whose rows `t̄` evaluate to `r`. -/
noncomputable def aggMS {D : Type u} (k : ℕ) (ts : List (Term D)) (v : ℕ → D) (P : List D → Prop)
    (r : List D) : ℕ∞ :=
  {ds : List D | ds.length = k ∧ P ds ∧ ts.map (Term.eval (vapp ds v)) = r}.encard

/-- The aggregation `ȳ ← ω(t̄; ḡ) φ` (Figure 1), where the group `ḡ` (all
    other free variables) is fixed by `v` and `P ds` states that `φ` holds for
    the values `ds` of the `k` aggregated variables: the group is non-empty
    and `v(ȳ) ∈ ω(M)`. -/
def aggSem {D : Type u} (k : ℕ) (ω : AggOp D) (ts : List (Term D)) (ys : List ℕ)
    (v : ℕ → D) (P : List D → Prop) : Prop :=
  (∃ ds : List D, ds.length = k ∧ P ds) ∧ ω.op (aggMS k ts v P) (ys.map v)

theorem aggSem_congr {D : Type u} {k : ℕ} {ω : AggOp D} {ts ts' : List (Term D)} {ys ys' : List ℕ}
    {v v' : ℕ → D} {P P' : List D → Prop}
    (hP : ∀ ds, ds.length = k → (P ds ↔ P' ds))
    (hts : ∀ ds, ds.length = k → ts.map (Term.eval (vapp ds v)) = ts'.map (Term.eval (vapp ds v')))
    (hys : ys.map v = ys'.map v') :
    aggSem k ω ts ys v P ↔ aggSem k ω ts' ys' v' P' := by
  have hM : aggMS k ts v P = aggMS k ts' v' P' := by
    funext r; unfold aggMS; congr 1; ext ds
    constructor
    · rintro ⟨hl, hp, hr⟩; exact ⟨hl, (hP ds hl).1 hp, (hts ds hl).symm.trans hr⟩
    · rintro ⟨hl, hp, hr⟩; exact ⟨hl, (hP ds hl).2 hp, (hts ds hl).trans hr⟩
  unfold aggSem
  rw [hM, hys]
  exact and_congr_left fun _ => exists_congr fun ds =>
    ⟨fun ⟨hl, hp⟩ => ⟨hl, (hP ds hl).1 hp⟩, fun ⟨hl, hp⟩ => ⟨hl, (hP ds hl).2 hp⟩⟩

/-- Drop the first `k` (bound) variables. -/
def shiftOut (k n : ℕ) : Option ℕ := if n < k then none else some (n - k)

/-! ## Events and predicates -/

/-- Event names: base events and the obligation events of let-bound
    predicates. -/
inductive Ev (B L : Type u) where
  | base : B → Ev B L
  | cau : L → Ev B L
  | sup : L → Ev B L
  deriving DecidableEq

/-- Predicates: events or let-bound predicates. -/
inductive Pr (B L : Type u) where
  | ev : Ev B L → Pr B L
  | lp : L → Pr B L

/-- A database: a set of events. -/
abbrev DB (B L D : Type u) := Set (Ev B L × List D)

/-- Membership in a (possibly unbounded) interval `[a, b]`. -/
def inI (a : ℕ) (b : Option ℕ) (n : ℕ) : Prop := a ≤ n ∧ ∀ b', b = some b' → n ≤ b'

/-! ## Traces -/

/-- A trace together with an interpretation of the let-bound predicates at
    every time-point. -/
structure Tr (B L D : Type u) where
  db : ℕ → DB B L D
  ts : ℕ → ℕ
  lv : ℕ → L → List D → Prop

namespace Tr
variable {B L D : Type u}

def prIn (σ : Tr B L D) (i : ℕ) : Pr B L → List D → Prop
  | .ev e, ds => (e, ds) ∈ σ.db i
  | .lp p, ds => σ.lv i p ds

end Tr

/-! ## MFOTL

MFOTL formulas (Section 2.2): events, equality, Boolean connectives,
quantification, the past operators `●_I` and `S_I` (hence `⧫_I`), the future
operators `○_I` and `◇_I`, and let bindings `let p(x̄) = φ in ψ`.  The
enforcer works on the let-normal form of these formulas (`Fm` below, computed
by `norm` in `LetNormal.lean`). -/

section
variable {B D : Type u}

/-- MFOTL formulas.  `upred k` refers to the `k`-th enclosing let binding
    (de Bruijn). -/
inductive MF (B D : Type u) where
  | tt : MF B D
  | pred : B → List (Term D) → MF B D
  | upred : ℕ → List (Term D) → MF B D
  | eq : Term D → Term D → MF B D
  | neg : MF B D → MF B D
  | conj : MF B D → MF B D → MF B D
  | ex : MF B D → MF B D
  | prev : ℕ → Option ℕ → MF B D → MF B D
  | since : ℕ → Option ℕ → MF B D → MF B D → MF B D
  | nx : ℕ → Option ℕ → MF B D → MF B D
  | ev : ℕ → ℕ → MF B D → MF B D
  | letin : ℕ → MF B D → MF B D → MF B D
  /-- `ȳ ← ω(t̄; ḡ) φ`: the first `k` variables of `φ` are aggregated over,
      its other free variables form the group `ḡ`, and the results are
      bound to the variables `ys`. -/
  | agg : ℕ → AggOp D → List (Term D) → List ℕ → MF B D → MF B D

namespace MF

/-- Semantics (Figure 1), on the base events of a trace, with `ρ` the
    interpretation of the enclosing let bindings. -/
def sat {L : Type u} (σ : Tr B L D) : List (ℕ → List D → Prop) → ℕ → (ℕ → D) → MF B D → Prop
  | _, _, _, tt => True
  | _, i, v, pred e ts => (Ev.base e, ts.map (Term.eval v)) ∈ σ.db i
  | ρ, i, v, upred k ts => ∃ P, ρ[k]? = some P ∧ P i (ts.map (Term.eval v))
  | _, _, v, eq t u => t.eval v = u.eval v
  | ρ, i, v, neg φ => ¬ sat σ ρ i v φ
  | ρ, i, v, conj φ ψ => sat σ ρ i v φ ∧ sat σ ρ i v ψ
  | ρ, i, v, ex φ => ∃ d, sat σ ρ i (vcons d v) φ
  | ρ, i, v, prev a b φ => 0 < i ∧ inI a b (σ.ts i - σ.ts (i - 1)) ∧ sat σ ρ (i - 1) v φ
  | ρ, i, v, since a b φ ψ => ∃ j ≤ i, inI a b (σ.ts i - σ.ts j) ∧ sat σ ρ j v ψ ∧
      ∀ k, j < k → k ≤ i → sat σ ρ k v φ
  | ρ, i, v, nx a b φ => inI a b (σ.ts (i + 1) - σ.ts i) ∧ sat σ ρ (i + 1) v φ
  | ρ, i, v, ev a b φ => ∃ j, i ≤ j ∧ a ≤ σ.ts j - σ.ts i ∧ σ.ts j - σ.ts i ≤ b ∧ sat σ ρ j v φ
  | ρ, i, v, letin ar body rest =>
    sat σ ((fun j as => as.length = ar ∧ sat σ ρ j (vapp as v) body) :: ρ) i v rest
  | ρ, i, v, agg k ω ts ys φ => aggSem k ω ts ys v (fun ds => sat σ ρ i (vapp ds v) φ)

/-- Free variables (let bodies are closed). -/
def fv : MF B D → List ℕ
  | tt => []
  | pred _ ts | upred _ ts => ts.flatMap Term.supp
  | eq t u => t.supp ++ u.supp
  | neg φ | prev _ _ φ | nx _ _ φ | ev _ _ φ => φ.fv
  | conj φ ψ | since _ _ φ ψ => φ.fv ++ ψ.fv
  | ex φ => φ.fv.filterMap fun n => match n with | 0 => none | n + 1 => some n
  | letin _ _ rest => rest.fv
  | agg k _ ts ys φ => (φ.fv ++ ts.flatMap Term.supp).filterMap (shiftOut k) ++ ys

/-- Well-formedness w.r.t. the arities `ars` of the enclosing lets: function
    terms read only their support, let-bound predicates are applied to the
    right number of arguments, and let bodies only use their parameters. -/
def WF : List ℕ → MF B D → Prop
  | _, tt => True
  | _, pred _ ts => ∀ t ∈ ts, t.WF
  | ars, upred k ts => ars[k]? = some ts.length ∧ ∀ t ∈ ts, t.WF
  | _, eq t u => t.WF ∧ u.WF
  | ars, neg φ | ars, ex φ | ars, prev _ _ φ | ars, nx _ _ φ | ars, ev _ _ φ => φ.WF ars
  | ars, conj φ ψ | ars, since _ _ φ ψ => φ.WF ars ∧ ψ.WF ars
  | ars, letin ar body rest => body.WF ars ∧ (∀ n ∈ body.fv, n < ar) ∧ rest.WF (ar :: ars)
  | ars, agg _ _ ts _ φ => φ.WF ars ∧ ∀ t ∈ ts, t.WF

/-- No future operators. -/
def ffree : MF B D → Prop
  | tt | pred _ _ | upred _ _ | eq _ _ => True
  | neg φ | ex φ | prev _ _ φ | agg _ _ _ _ φ => φ.ffree
  | conj φ ψ | since _ _ φ ψ | letin _ φ ψ => φ.ffree ∧ ψ.ffree
  | nx _ _ _ | ev _ _ _ => False

/-- Past operators and let bodies do not contain future operators. -/
def PastPure : MF B D → Prop
  | tt | pred _ _ | upred _ _ | eq _ _ => True
  | neg φ | ex φ | nx _ _ φ | ev _ _ φ => φ.PastPure
  | conj φ ψ => φ.PastPure ∧ ψ.PastPure
  | prev _ _ φ => φ.ffree ∧ φ.PastPure
  | since _ _ φ ψ => φ.ffree ∧ ψ.ffree ∧ φ.PastPure ∧ ψ.PastPure
  | letin _ body rest => body.ffree ∧ body.PastPure ∧ rest.PastPure
  | agg _ _ _ _ φ => φ.ffree ∧ φ.PastPure

end MF

end

/-! ## Let-normal form

Formulas in let-normal form (Section 4.1): past operators only occur at the
top of let bodies, and are referenced through let-bound predicates
`pred (.lp p)`; future operators may occur in the enforced formula. -/

/-- MFOTL formulas in let-normal form: past operators are let-bound (and
    referenced through `pred (.lp p)`); future operators `◇_[a,b]` and
    `○_[a,b]` may occur in the enforced body. -/
inductive Fm (B L D : Type u) where
  | tt : Fm B L D
  | pred : Pr B L → List (Term D) → Fm B L D
  | eq : Term D → Term D → Fm B L D
  | neg : Fm B L D → Fm B L D
  | conj : Fm B L D → Fm B L D → Fm B L D
  | ex : Fm B L D → Fm B L D
  | ev : ℕ → ℕ → Fm B L D → Fm B L D
  | nx : ℕ → Option ℕ → Fm B L D → Fm B L D

namespace Fm
variable {B L D : Type u}

def disj (φ ψ : Fm B L D) : Fm B L D := neg (conj (neg φ) (neg ψ))

def subst (s : ℕ → Term D) : Fm B L D → Fm B L D
  | tt => tt
  | pred p ts => pred p (ts.map (Term.subst s))
  | eq t u => eq (t.subst s) (u.subst s)
  | neg φ => neg (φ.subst s)
  | conj φ ψ => conj (φ.subst s) (ψ.subst s)
  | ex φ => ex (φ.subst (upS s))
  | ev a b φ => ev a b (φ.subst s)
  | nx a b φ => nx a b (φ.subst s)

/-- Present (future-free) formulas: these can be evaluated on a single
    database. -/
def present : Fm B L D → Prop
  | tt | pred _ _ | eq _ _ => True
  | neg φ | ex φ => φ.present
  | conj φ ψ => φ.present ∧ ψ.present
  | ev _ _ _ | nx _ _ _ => False

theorem present_subst (s : ℕ → Term D) (φ : Fm B L D) (h : φ.present) :
    (φ.subst s).present := by
  induction φ generalizing s with
  | conj φ ψ ih1 ih2 => exact ⟨ih1 _ h.1, ih2 _ h.2⟩
  | neg φ ih => exact ih _ h
  | ex φ ih => exact ih _ h
  | _ => simp_all [subst, present]

end Fm

namespace Tr
variable {B L D : Type u}

/-- The satisfaction relation `v, i ⊨_σ φ`. -/
def sat (σ : Tr B L D) : ℕ → (ℕ → D) → Fm B L D → Prop
  | _, _, .tt => True
  | i, v, .pred p ts => σ.prIn i p (ts.map (Term.eval v))
  | _, v, .eq t u => t.eval v = u.eval v
  | i, v, .neg φ => ¬ σ.sat i v φ
  | i, v, .conj φ ψ => σ.sat i v φ ∧ σ.sat i v ψ
  | i, v, .ex φ => ∃ d, σ.sat i (vcons d v) φ
  | i, v, .ev a b φ => ∃ j, i ≤ j ∧ a ≤ σ.ts j - σ.ts i ∧ σ.ts j - σ.ts i ≤ b ∧ σ.sat j v φ
  | i, v, .nx a b φ => inI a b (σ.ts (i + 1) - σ.ts i) ∧ σ.sat (i + 1) v φ

@[simp] theorem sat_disj (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (φ ψ : Fm B L D) :
    σ.sat i v (φ.disj ψ) ↔ σ.sat i v φ ∨ σ.sat i v ψ := by
  simp [Fm.disj, sat]; tauto

theorem sat_subst (σ : Tr B L D) (φ : Fm B L D) :
    ∀ (i : ℕ) (v : ℕ → D) (s : ℕ → Term D),
      σ.sat i v (φ.subst s) ↔ σ.sat i (fun n => (s n).eval v) φ := by
  induction φ with
  | tt => intros; rfl
  | pred p ts =>
    intro i v s
    simp only [Fm.subst, sat, List.map_map]
    have : (Term.eval v ∘ Term.subst s) = Term.eval (fun n => (s n).eval v) := by
      funext t; simp
    rw [this]
  | eq t u => intro i v s; simp [Fm.subst, sat]
  | neg φ ih => intro i v s; simp [Fm.subst, sat, ih]
  | conj φ ψ ih1 ih2 => intro i v s; simp [Fm.subst, sat, ih1, ih2]
  | ex φ ih =>
    intro i v s
    simp only [Fm.subst, sat, ih, eval_upS]
  | ev a b φ ih => intro i v s; simp [Fm.subst, sat, ih]
  | nx a b φ ih => intro i v s; simp [Fm.subst, sat, ih]

/-- Present formulas only depend on the current database and let
    interpretation. -/
theorem sat_present (σ σ' : Tr B L D) (i i' : ℕ) (hdb : σ.db i = σ'.db i')
    (hlv : σ.lv i = σ'.lv i') (φ : Fm B L D) (hφ : φ.present) :
    ∀ v, σ.sat i v φ ↔ σ'.sat i' v φ := by
  induction φ with
  | tt => intro; rfl
  | pred p ts => intro v; cases p <;> simp [sat, prIn, hdb, hlv]
  | eq => intro; rfl
  | neg φ ih => intro v; simp [sat, ih hφ]
  | conj φ ψ ih1 ih2 => intro v; simp [sat, ih1 hφ.1, ih2 hφ.2]
  | ex φ ih => intro v; simp [sat, ih hφ]
  | ev => exact absurd hφ id
  | nx => exact absurd hφ id

end Tr

/-! ### Let bindings -/

section
variable {B L D : Type u}

/-- Bodies of let bindings in let-normal form (`Once_I φ = ⊤ S_I φ`):
    present formulas (`let`), since (`table`), previous (`lagged table`), and
    aggregations (`agg let`, with the results at argument positions `ys`). -/
inductive LBody (B L D : Type u) where
  | now : Fm B L D → LBody B L D
  | since : ℕ → Option ℕ → Fm B L D → Fm B L D → LBody B L D
  | prev : ℕ → Option ℕ → Fm B L D → LBody B L D
  | agg : ℕ → AggOp D → List (Term D) → List ℕ → Fm B L D → LBody B L D

namespace LBody

/-- MFOTL semantics of a let body at time-point `i` under valuation `w`. -/
def sem (σ : Tr B L D) (i : ℕ) (w : ℕ → D) : LBody B L D → Prop
  | now φ => σ.sat i w φ
  | since a b φl φr => ∃ j ≤ i, inI a b (σ.ts i - σ.ts j) ∧ σ.sat j w φr ∧
      ∀ k, j < k → k ≤ i → σ.sat k w φl
  | prev a b φ => 0 < i ∧ inI a b (σ.ts i - σ.ts (i - 1)) ∧ σ.sat (i - 1) w φ
  | agg k ω ts ys φ => aggSem k ω ts ys w (fun ds => σ.sat i (vapp ds w) φ)

end LBody

structure LetDef (B L D : Type u) where
  arity : ℕ
  body : LBody B L D

/-- The let-bound predicates are interpreted according to their definitions
    (relative to a fixed valuation `v₀` of the context). -/
def LetSem (Γ : L → Option (LetDef B L D)) (σ : Tr B L D) (v₀ : ℕ → D) : Prop :=
  ∀ p d, Γ p = some d → ∀ i (as : List D), as.length = d.arity →
    (σ.lv i p as ↔ d.body.sem σ i (vapp as v₀))

end

end Enfflash
