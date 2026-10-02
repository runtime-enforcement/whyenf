/-
  §3.1 EF syntax (main.tex l.718–842, Figure 3), as abstract syntax.

  Identifiers are typed by their role: names of events, tables and lets are
  in `ℰ` (Algorithm 2 interprets all of them by one map `R : ℰ ⇀ 𝒫(𝔻*)`,
  l.860), variables (column names, clause variables) are in `𝕍`, function
  names in `𝔽`, aggregation operators (built-in or `tfun`) in `Ω`.
  Python code is opaque text: its only role in the semantics is that each
  `fun` declaration "associates a function `f̂` to the function symbol `f`"
  (l.858), i.e. the `f̂` of the vocabulary, and each `tfun` an operator `ω̂`.
-/
import Paper.MFOTL

namespace Paper

variable (Voc : Vocabulary)

/-- `X (sep X)*`: a non-empty list. -/
structure NList (α : Type) where
  head : α
  tail : List α

def NList.toList {α : Type} (l : NList α) : List α := l.head :: l.tail

/-- `τ ::= int ∣ float ∣ str ∣ bool` -/
inductive Ty | int | float | str | bool

/-- `c ::= id : τ` -/
structure Col where
  name : Voc.𝕍
  ty : Ty

/-- `ℓ ::= @id` -/
structure Label where
  id : String

/-- `b ::= n ∣ *` (`*` is `⊤ = ∞`). -/
abbrev Bound := ℕ∞

/-- Python code (opaque). -/
structure Python where
  code : String

/-- `evdecl ::= event id(τ̄);` -/
structure EvDecl where
  id : Voc.ℰ
  tys : List Ty

/-- `pyinit ::= pyinit { python }` -/
structure PyInit where
  code : Python

/-- `fun ::= fun id(c̄) : τ { python }` -/
structure FunDecl where
  id : Voc.𝔽
  params : List (Col Voc)
  ret : Ty
  code : Python

/-- `tfun ::= tfun id { python }` -/
structure TFunDecl where
  id : Voc.Ω
  code : Python

/-- An argument `id ∣ v` of a guard atom. -/
inductive GArg where
  | var : Voc.𝕍 → GArg
  | val : Voc.𝔻 → GArg

/-- `γ ::= id(id ∣ v, …) ∣ id == v` -/
inductive Atom where
  | pred : Voc.ℰ → List (GArg Voc) → Atom
  | eq : Voc.𝕍 → Voc.𝔻 → Atom

/-- `κ ::= γ (& γ)*` -/
abbrev EGuard := NList (Atom Voc)

/-- `π ::= κ (or κ)*` -/
abbrev EGuards := NList (EGuard Voc)

/-- Filters `φ ::= true ∣ false ∣ id(t̄) ∣ φ & φ ∣ φ | φ ∣ !φ` with terms
    `t ::= id ∣ const ∣ id(t̄)` (the MFOTL terms). -/
inductive Filter where
  | tt : Filter
  | ff : Filter
  | pred : Voc.ℰ → List (Term Voc) → Filter
  | and : Filter → Filter → Filter
  | or : Filter → Filter → Filter
  | not : Filter → Filter

/-- `cl ::= π [if φ] ∣ if φ` -/
inductive Clause where
  | guarded : EGuards Voc → Option (Filter Voc) → Clause
  | filter : Filter Voc → Clause

/-- `(+ ∣ −)` -/
inductive Sign | plus | minus
  deriving DecidableEq

/-- `(fixpoint ∣ once)` -/
inductive SecKind | fixpoint | once
  deriving DecidableEq

/-- `item ::= table ∣ let ∣ agg ∣ rule ∣ sec` -/
inductive Item where
  /-- `[ℓ] [lagged] table id(c̄) [[window n b]] := add {cl} [remove {cl}];` -/
  | table (ℓ : Option Label) (lagged : Bool) (id : Voc.ℰ) (cols : List (Col Voc))
      (window : Option (ℕ × Bound)) (add : Clause Voc) (remove : Option (Clause Voc))
  /-- `[ℓ] [filter] let id(c̄) := {cl};` -/
  | let_ (ℓ : Option Label) (filter : Bool) (id : Voc.ℰ) (cols : List (Col Voc)) (c : Clause Voc)
  /-- `[ℓ] agg let id(c̄) := id(t̄) group_by id̄ over {cl};` -/
  | agg (ℓ : Option Label) (id : Voc.ℰ) (cols : List (Col Voc)) (op : Voc.Ω)
      (args : List (Term Voc)) (groupBy : List Voc.𝕍) (overCl : Clause Voc)
  /-- `[ℓ] rule (+ ∣ −) id(t̄) [[delay n]] [[next n]] := trigger {cl};` -/
  | rule (ℓ : Option Label) (sign : Sign) (id : Voc.ℰ) (args : List (Term Voc))
      (delay : Option ℕ) (next : Option ℕ) (trigger : Clause Voc)
  /-- `section (fixpoint ∣ once);` -/
  | sec (kind : SecKind)

/-- `prog ::= evdecl* [pyinit] fun* tfun* item*` -/
structure Program where
  evdecls : List (EvDecl Voc)
  pyinit : Option PyInit
  funs : List (FunDecl Voc)
  tfuns : List (TFunDecl Voc)
  items : List (Item Voc)

end Paper
