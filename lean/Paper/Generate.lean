/-
  §4.1 Let-normal form (main.tex l.1127–1145) and §4.4 Algorithm 3
  (l.1376–1468).
-/
import Paper.Rewrite

namespace Paper

variable {Voc : Vocabulary}

/-! ## §4.1 Let-normal form -/

namespace Formula

/-- Contains a future operator (`○`, `◇`). -/
def HasFuture : Formula Voc → Prop
  | .next _ _ => True
  | .eventually _ _ => True
  | .neg φ => φ.HasFuture
  | .and φ ψ => φ.HasFuture ∨ ψ.HasFuture
  | .ex _ φ => φ.HasFuture
  | .prev _ φ => φ.HasFuture
  | .since _ φ ψ => φ.HasFuture ∨ ψ.HasFuture
  | .letin _ _ φ ψ => φ.HasFuture ∨ ψ.HasFuture
  | .agg _ _ _ _ φ => φ.HasFuture
  | _ => False

/-- `χ`: "an MFOTL formula without any quantifiers (except over subformulae with
    future operators), `●` and `S_I` operators, or aggregation/table operators"
    (l.1136–1137).  `χ` contains no `let` either: all lets are at the top. -/
def IsChi : Formula Voc → Prop
  | .top => True
  | .pred _ _ => True
  | .eq _ _ => True
  | .neg φ => φ.IsChi
  | .and φ ψ => φ.IsChi ∧ ψ.IsChi
  | .ex _ φ => φ.HasFuture ∧ φ.IsChi
  | .next _ φ => φ.IsChi
  | .eventually _ φ => φ.IsChi
  | .prev _ _ => False
  | .since _ _ _ => False
  | .letin _ _ _ _ => False
  | .agg _ _ _ _ _ => False

/-- `∃y₁, …, y_k. χ` -/
def exs (ys : List Voc.𝕍) (χ : Formula Voc) : Formula Voc := ys.foldr Formula.ex χ

/-- `ψ = ∃y₁, …, y_k. χ` (l.1135). -/
def IsPsi (ψ : Formula Voc) : Prop := ∃ ys χ, ψ = exs ys χ ∧ χ.IsChi

/-- A let body `φᵢ`: one of `ψ`, `●_I ψ`, `ψ_l S_I ψ_r`, `ȳ ← ω(t̄; ḡ) ψ` (l.1135). -/
def IsLetBody (φ : Formula Voc) : Prop :=
  φ.IsPsi ∨ (∃ I ψ, φ = .prev I ψ ∧ ψ.IsPsi) ∨
    (∃ I ψl ψr, φ = .since I ψl ψr ∧ ψl.IsPsi ∧ ψr.IsPsi) ∨
    (∃ ys ω ts gs ψ, φ = .agg ys ω ts gs ψ ∧ ψ.IsPsi)

end Formula

/-- A let binding `e(x̄) = φ`. -/
structure LetDef (Voc : Vocabulary) where
  e : Voc.ℰ
  xs : List Voc.𝕍
  φ : Formula Voc

/-- A formula in let-normal form
    `let e₁(x̄₁) = φ₁ in … let e_m(x̄_m) = φ_m in □χ₁ ∧ … ∧ □χ_n` (l.1131–1134),
    given by its lets `ℒ` and its body formulas `χ₁, …, χ_n`. -/
structure LNF (Voc : Vocabulary) where
  lets : List (LetDef Voc)
  chis : List (Formula Voc)

def LNF.Valid (L : LNF Voc) : Prop :=
  (∀ d ∈ L.lets, d.φ.IsLetBody) ∧ L.chis ≠ [] ∧ ∀ χ ∈ L.chis, χ.IsChi

/-- The body `□χ₁ ∧ … ∧ □χ_n`. -/
def LNF.body (L : LNF Voc) : Formula Voc := bigAnd (L.chis.map Formula.Always)

def LNF.toFormula (L : LNF Voc) : Formula Voc :=
  L.lets.foldr (fun d acc => .letin d.e d.xs d.φ acc) L.body

/-! ### Theorem 4.1, over a signature extended with fresh let names -/

/-- `Voc` extended with a finite set `L` of fresh event names (the let names),
    with arities `ιL`. -/
def Vocabulary.ext (Voc : Vocabulary) (L : Type) [Finite L] (ιL : L → ℕ) : Vocabulary where
  𝔻 := Voc.𝔻
  ℰ := Voc.ℰ ⊕ L
  finE := by haveI := Voc.finE; infer_instance
  ι := Sum.elim Voc.ι ιL
  𝕍 := Voc.𝕍
  decV := Voc.decV
  𝔽 := Voc.𝔽
  ιF := Voc.ιF
  fhat := Voc.fhat
  Ω := Voc.Ω
  ι' := Voc.ι'
  ωhat := Voc.ωhat

section ext
variable {L : Type} [Finite L] {ιL : L → ℕ}

mutual
def Term.embed : Term Voc → Term (Voc.ext L ιL)
  | .var x => .var x
  | .const c => .const c
  | .app f ts => .app f (Term.embedList ts)
def Term.embedList : List (Term Voc) → List (Term (Voc.ext L ιL))
  | [] => []
  | t :: ts => Term.embed t :: Term.embedList ts
end

/-- A formula over `Voc` as a formula over the extended vocabulary. -/
def Formula.embed : Formula Voc → Formula (Voc.ext L ιL)
  | .top => .top
  | .pred e ts => .pred (Sum.inl e) (Term.embedList ts)
  | .neg φ => .neg φ.embed
  | .and φ ψ => .and φ.embed ψ.embed
  | .ex x φ => .ex x φ.embed
  | .next I φ => .next I φ.embed
  | .prev I φ => .prev I φ.embed
  | .eventually I φ => .eventually I φ.embed
  | .since I φ ψ => .since I φ.embed ψ.embed
  | .letin e xs φ ψ => .letin (Sum.inl e) xs φ.embed ψ.embed
  | .agg ys ω ts gs φ => .agg ys ω (Term.embedList ts) gs φ.embed
  | .eq x c => .eq x c

/-- A structure over `Voc` as one over the extended vocabulary (no events
    with the new names). -/
def Str.embed (σ : Str Voc.toSignature) : Str (Voc.ext L ιL).toSignature where
  τ := σ.τ
  D := fun j => {ev | ∃ ev' ∈ σ.D j, ev.e = Sum.inl ev'.e ∧ ev.args = ev'.args}

end ext

/-- The lets of `L` bind only fresh names (`Sum.inr`). -/
def LNF.FreshLets {L : Type} [Finite L] {ιL : L → ℕ} (N : LNF (Voc.ext L ιL)) : Prop :=
  ∀ d ∈ N.lets, ∃ l, d.e = Sum.inr l

/-! ## §4.4 Algorithm 3 -/

/-- `StripExists(∃y₁ … y_k. χ) = χ`. -/
def stripExists : Formula Voc → Formula Voc
  | .ex _ φ => stripExists φ
  | φ => φ

/-- `gate^ℂ_p(𝒞)` / `gate^𝕊_p(𝒞)`: conjoin the atom `Cau_p(x̄)` (resp. `Sup_p(x̄)`)
    to every guard of `𝒞` (l.1380–1383). -/
def gate (q : Voc.ℰ) (xs : List Voc.𝕍) (𝒞 : CSet Voc) : CSet Voc :=
  𝒞.map fun π ψ ε => ⟨π.map (· ++ [.pred q (xs.map Term.var)]), ψ, ε⟩

/-- The output of `TypeLet` for one let: `Γ(p)` and the two clause families
    `𝒞^ℂ(p)`, `𝒞^𝕊(p)` (which Algorithm 3 assigns but does not return). -/
structure Typed (Voc : Vocabulary) where
  Γ : LetCtx Voc
  CC : Voc.ℰ → CSet Voc
  CS : Voc.ℰ → CSet Voc

section
open Classical

/-- `TypeLet(Γ, p, x̄, ψ)` (l.1410–1442).  `none` is `reject`.

    `m ← m_Γ`, the base events and the lets with `g = ⊤`; `𝒞^ℂ(p)` and
    `𝒞^𝕊(p)` are initially `∅`.  In the `⧫_[a,b]` and `S_[a,b]` cases, `a = 0`
    is `0 ∈ [a, b]`. -/
noncomputable def TypeLet (Ξ : RwSetting Voc) (T : Typed Voc) (p : Voc.ℰ) (xs : List Voc.𝕍)
    (ψ : Formula Voc) : Option (Typed Voc) :=
  let Γ := T.Γ
  let χ := stripExists ψ
  let m : Set Voc.ℰ := Ξ.m Γ
  let X : Set Voc.𝕍 := {x | x ∈ xs} ∪ χ.fv
  let ret (CC CS : CSet Voc) : Option (Typed Voc) :=
    some ⟨Function.update Γ p (some (true, decide (CC ≠ ∅), decide (CS ≠ ∅))),
      Function.update T.CC p CC, Function.update T.CS p CS⟩
  match χ with
  | .since I .top φ =>
    -- `case ⧫_[a,b] φ` (`a = 0` iff `0 ∈ [a, b]`)
    if Guards m φ.fv φ = none then none
    else ret (if 0 ∈ I then gate (Ξ.cauN p) xs (RwAll Ξ Γ .C φ) else ∅) ∅
  | .prev _ φ | .agg _ _ _ _ φ =>
    -- `case ●φ ∣ Agg(…, φ)`
    if Guards m φ.fv φ = none then none else ret ∅ ∅
  | .since I φl φr =>
    -- `case φ_l S_[a,b] φ_r`
    if Guards m X (.neg φl) = none ∨ Guards m X φr = none then none
    else if 0 ∈ I then
      ret (gate (Ξ.cauN p) xs (RwAll Ξ Γ .C φr))
        (gate (Ξ.supN p) xs ((RwAll Ξ Γ .S φl).tensor (RwAll Ξ Γ .S φr)))
    else ret ∅ (gate (Ξ.supN p) xs (RwAll Ξ Γ .S φl))
  | _ =>
    -- `case otherwise`; the clause families are only computed if `χ` is present.
    if Guards m X χ = none then
      some ⟨Function.update Γ p (some (false, false, false)), T.CC, T.CS⟩
    else if χ.Present then
      ret (gate (Ξ.cauN p) xs (RwAll Ξ Γ .C ψ)) (gate (Ξ.supN p) xs (RwAll Ξ Γ .S ψ))
    else ret ∅ ∅

end

/-- `Realizations(Γ, C)` (l.1462–1466): the least clause sets `R ⊇ C` such
    that, for some choice `f(p) ∈ 𝒞^ℂ(p)`, `g(p) ∈ 𝒞^𝕊(p)`, `f(p) ⊆ R`
    (`g(p) ⊆ R`) whenever the effect of a clause of `R` is on `Cau_p`
    (`Sup_p`), possibly under `◇` or `○`. -/
def Realizations (Ξ : RwSetting Voc) (T : Typed Voc) (C : Set (EClause Voc)) :
    Set (Set (EClause Voc)) :=
  {R | ∃ f g : Voc.ℰ → Set (EClause Voc),
    let Closed (R' : Set (EClause Voc)) : Prop :=
      C ⊆ R' ∧ ∀ c ∈ R', ∀ p,
        (c.ε.name = Ξ.cauN p → f p ∈ T.CC p ∧ f p ⊆ R') ∧
        (c.ε.name = Ξ.supN p → g p ∈ T.CS p ∧ g p ⊆ R')
    Closed R ∧ ∀ R', Closed R' → R ⊆ R'}

/-- `Γ ← ∅; for all (p(x̄) := ψ) ∈ ℒ do Γ ← TypeLet(Γ, p, x̄, ψ)` (Algorithm 3,
    lines 2–3); `none` if some `TypeLet` rejects. -/
noncomputable def TypeLets (Ξ : RwSetting Voc) (ℒ : List (LetDef Voc)) : Option (Typed Voc) :=
  ℒ.foldlM (fun T d => TypeLet Ξ T d.e d.xs d.φ) ⟨fun _ => none, fun _ => ∅, fun _ => ∅⟩

/-- `Generate(□φ)` (l.1403–1408), for a given `LetNormalForm` function that
    computes a let-normal form as in §4.1 (NOTES.md, F6), and
    `φ♭ = χ₁ ∧ … ∧ χ_n`.  `none` if some `TypeLet` rejects. -/
noncomputable def Generate (Ξ : RwSetting Voc) (LetNormalForm : Formula Voc → LNF Voc)
    (φ : Formula Voc) : Option (Set (Set (EClause Voc))) :=
  let L := LetNormalForm (Formula.Always φ)
  (TypeLets Ξ L.lets).map fun T =>
    {R | ∃ 𝒞, Rw Ξ T.Γ .C (bigAnd L.chis) 𝒞 ∧ ∃ C ∈ 𝒞, R ∈ Realizations Ξ T C}

end Paper
