/-
  §4.2 Guard extraction (main.tex l.1160–1233, Figure 4, Lemma 4.2).
-/
import Paper.MFOTL

namespace Paper

variable {Voc : Vocabulary}

/-! ## Guards -/

/-- A guard atom: an event `p(t̄)` or an equation `x = c`. -/
inductive GAtom (Voc : Vocabulary) where
  | pred : Voc.ℰ → List (Term Voc) → GAtom Voc
  | eq : Voc.𝕍 → Voc.𝔻 → GAtom Voc

/-- A guard `κ`: a conjunction of atoms (`⊤` is the empty conjunction). -/
abbrev GConj (Voc : Vocabulary) := List (GAtom Voc)

/-- A disjunction of guards `π = ⋁ᵢ κᵢ` (l.1165).  `{⊤}` is `[[]]`, `∅` is `[]`. -/
abbrev GDisj (Voc : Vocabulary) := List (GConj Voc)

def GAtom.toFormula : GAtom Voc → Formula Voc
  | .pred p ts => .pred p ts
  | .eq x c => .eq x c

/-- `⋀_{γ ∈ κ} γ` -/
def GConj.toFormula (κ : GConj Voc) : Formula Voc :=
  κ.foldr (fun γ φ => .and γ.toFormula φ) .top

/-- `⋁_{κ ∈ π} κ` -/
def GDisj.toFormula (π : GDisj Voc) : Formula Voc :=
  π.foldr (fun κ φ => Formula.or κ.toFormula φ) .bot

/-- `{κ₁ ∧ κ₂ ∣ κ₁ ∈ π₁, κ₂ ∈ π₂}` -/
def GDisj.prod (π₁ π₂ : GDisj Voc) : GDisj Voc :=
  π₁.flatMap fun κ₁ => π₂.map fun κ₂ => κ₁ ++ κ₂

/-- `κ` binds `x`: `κ` contains an atom with argument `x` (Appendix A, l.2118). -/
def GConj.Binds (κ : GConj Voc) (x : Voc.𝕍) : Prop :=
  ∃ γ ∈ κ, (∃ p ts, γ = .pred p ts ∧ Term.var x ∈ ts) ∨ (∃ c, γ = .eq x c)

/-! ## Figure 4 -/

/-- Polarities `p ∈ {+, −}`. -/
inductive Pol | pos | neg
  deriving DecidableEq

def Pol.flip : Pol → Pol
  | .pos => .neg
  | .neg => .pos

/-- `m ⊢ Φ ⇝^p_X (π, φ)` (Figure 4). -/
inductive GX (m : Set Voc.ℰ) : Pol → Set Voc.𝕍 → Formula Voc → GDisj Voc → Formula Voc → Prop
  /-- `None`: `m ⊢ Φ ⇝^p_∅ ({⊤}, Φ)` -/
  | none (p : Pol) (Φ : Formula Voc) : GX m p ∅ Φ [[]] Φ
  /-- `Vac`: `m ⊢ ⊤ ⇝⁻_X (∅, ⊤)` -/
  | vac (X : Set Voc.𝕍) : GX m .neg X .top [] .top
  /-- `Pred`: `p ∈ m`, `X ⊆ t̄` -/
  | pred (X : Set Voc.𝕍) (p : Voc.ℰ) (ts : List (Term Voc)) :
      p ∈ m → (∀ x ∈ X, Term.var x ∈ ts) → GX m .pos X (.pred p ts) [[.pred p ts]] .top
  /-- `Eq`: `X ⊆ {x}` -/
  | eq (X : Set Voc.𝕍) (x : Voc.𝕍) (c : Voc.𝔻) :
      X ⊆ {x} → GX m .pos X (.eq x c) [[.eq x c]] .top
  /-- `And⁺` -/
  | andPos {X X₁ X₂ : Set Voc.𝕍} {φ ψ φ' ψ' : Formula Voc} {π₁ π₂ : GDisj Voc} :
      GX m .pos X₁ φ π₁ φ' → GX m .pos X₂ ψ π₂ ψ' → X ⊆ X₁ ∪ X₂ →
      GX m .pos X (.and φ ψ) (π₁.prod π₂) (.and φ' ψ')
  /-- `And⁻` -/
  | andNeg {X : Set Voc.𝕍} {φ ψ φ' ψ' : Formula Voc} {π₁ π₂ : GDisj Voc} :
      GX m .neg X φ π₁ φ' → GX m .neg X ψ π₂ ψ' →
      GX m .neg X (.and φ ψ) (π₁ ++ π₂) (.and (.imp π₁.toFormula φ') (.imp π₂.toFormula ψ'))
  /-- `Neg` -/
  | neg {p : Pol} {X : Set Voc.𝕍} {φ φ' : Formula Voc} {π : GDisj Voc} :
      GX m p.flip X φ π φ' → GX m p X (.neg φ) π (.neg φ')

/-- `Guards^m_X(Φ) = (π, φ)` if `m ⊢ Φ ⇝⁺_X (π, φ)`, and `⊥` (`none`) if no
    such derivation exists (l.1189–1192), for a fixed choice among several
    derivations (NOTES.md, F11). -/
noncomputable def Guards (m : Set Voc.ℰ) (X : Set Voc.𝕍) (Φ : Formula Voc) :
    Option (GDisj Voc × Formula Voc) :=
  open Classical in
  if h : ∃ r : GDisj Voc × Formula Voc, GX m .pos X Φ r.1 r.2 then some (Classical.choose h) else none

/-! ## Lemma 4.2 -/

/-- `φ ≡ ψ`: equivalence under every structure, valuation and time-point. -/
def Equiv (φ ψ : Formula Voc) : Prop := ∀ σ v i, φ.sat σ v i ↔ ψ.sat σ v i

end Paper
