/-
  Enfflash formalization — guard extraction (paper, Section 4.2, Figure 4).
-/
import Enfflash.EF

namespace Enfflash

universe u
variable {B L D : Type u}

/-! ## Guard extraction (Figure 4, with corrected vacuous rules)

`GX m x p (π, φ) (π', φ')` extracts a guard for variable `x`.  For polarity
`true` the pair denotes `π ∧ φ`; for `false` it denotes `π ∧ ¬φ` (i.e. the
negation of the implication `π → φ`).

The paper's rule `Vac` reads `(π, ⊤) ↝⁺ (π, ⊤)`, which invalidates the lemma
that `x` is bound in every resulting guard.  The correct vacuous cases are
`(π, ⊥) ↝⁺ (∅, ⊥)` and `(π, ⊤) ↝⁻ (∅, ⊤)`: the trigger can never fire, so the
empty disjunction of guards is an equivalent (and trivially guarded) choice.
-/

def polSat (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (p : Bool) (π : Guards B L D)
    (φ : Fm B L D) : Prop :=
  π.sat σ i v ∧ (if p then σ.sat i v φ else ¬ σ.sat i v φ)

/-- Equivalence of guarded formulas at polarity `p`: `⋁π ∧ φ ≡ ⋁π' ∧ φ'`
    (`p = true`), resp. `⋁π ∧ ¬φ ≡ ⋁π' ∧ ¬φ'` (`p = false`). -/
abbrev GEquiv (p : Bool) (π : Guards B L D) (φ : Fm B L D) (π' : Guards B L D)
    (φ' : Fm B L D) : Prop :=
  ∀ σ i v, polSat σ i v p π φ ↔ polSat σ i v p π' φ'

/-- `π → φ` as a formula. -/
def impFm (π : Guards B L D) (φ : Fm B L D) : Fm B L D := Fm.disj (.neg π.toFm) φ

inductive GX (m : Pr B L → Prop) (x : ℕ) :
    Bool → Guards B L D → Fm B L D → Guards B L D → Fm B L D → Prop
  | grd {p π φ} : Guards.bindsAll x π → GX m x p π φ π φ
  | vacPos {π} : GX m x true π (.neg .tt) [] (.neg .tt)
  | vacNeg {π} : GX m x false π .tt [] .tt
  | pred {π p ts} : m p → Term.var x ∈ ts →
      GX m x true π (.pred p ts) (π.addAtom (.pred p ts)) .tt
  | eq {π d} : GX m x true π (.eq (.var x) (.const d)) (π.addAtom (.eq (.var x) d)) .tt
  | neg {p π φ π' φ'} : GX m x (!p) π φ π' φ' → GX m x p π (.neg φ) π' (.neg φ')
  | andL {π φ ψ π' φ'} : GX m x true π φ π' φ' → GX m x true π (.conj φ ψ) π' (.conj φ' ψ)
  | andR {π φ ψ π' ψ'} : GX m x true π ψ π' ψ' → GX m x true π (.conj φ ψ) π' (.conj φ ψ')
  | andNeg {π φ ψ π₁ φ₁ π₂ ψ₂} : GX m x false π φ π₁ φ₁ → GX m x false π ψ π₂ ψ₂ →
      GX m x false π (.conj φ ψ) (π₁ ++ π₂) (.conj (impFm π₁ φ₁) (impFm π₂ ψ₂))

namespace GX
variable {m : Pr B L → Prop} {x : ℕ}

private theorem andNeg_prop {P F G P₁ F₁ P₂ G₂ : Prop}
    (h1 : P ∧ ¬F ↔ P₁ ∧ ¬F₁) (h2 : P ∧ ¬G ↔ P₂ ∧ ¬G₂) :
    (P ∧ ¬(F ∧ G)) ↔ ((P₁ ∨ P₂) ∧ ¬((¬P₁ ∨ F₁) ∧ (¬P₂ ∨ G₂))) := by
  by_cases hP : P <;> by_cases hF : F <;> by_cases hG : G <;>
    by_cases hP₁ : P₁ <;> by_cases hF₁ : F₁ <;> by_cases hP₂ : P₂ <;> by_cases hG₂ : G₂ <;>
    simp_all

/-- **Lemma 4.2** (guard extraction): the rewritten pair is equivalent, and `x` is
    bound in every resulting guard. -/
theorem sound {p : Bool} {π π' : Guards B L D} {φ φ' : Fm B L D} (h : GX m x p π φ π' φ') :
    GEquiv p π φ π' φ' ∧ π'.bindsAll x := by
  induction h with
  | grd hb => exact ⟨fun _ _ _ => Iff.rfl, hb⟩
  | vacPos => exact ⟨fun σ i v => by simp [polSat, Tr.sat, Guards.sat], by simp [Guards.bindsAll]⟩
  | vacNeg => exact ⟨fun σ i v => by simp [polSat, Tr.sat, Guards.sat], by simp [Guards.bindsAll]⟩
  | @pred π p ts _ hx =>
    refine ⟨fun σ i v => ?_, ?_⟩
    · simp [polSat, Guards.sat_addAtom, Tr.sat, GAtom.sat]
    · intro κ hκ
      simp only [Guards.addAtom, List.mem_map] at hκ
      obtain ⟨κ₀, -, rfl⟩ := hκ
      exact ⟨.pred p ts, by simp, hx⟩
  | @eq π d =>
    refine ⟨fun σ i v => ?_, ?_⟩
    · simp [polSat, Guards.sat_addAtom, Tr.sat, GAtom.sat, Term.eval]
    · intro κ hκ
      simp only [Guards.addAtom, List.mem_map] at hκ
      obtain ⟨κ₀, -, rfl⟩ := hκ
      exact ⟨.eq (.var x) d, by simp, rfl⟩
  | @neg p π φ π' φ' _ ih =>
    refine ⟨fun σ i v => ?_, ih.2⟩
    have := ih.1 σ i v
    cases p <;> simp_all [polSat, Tr.sat]
  | andL _ ih =>
    refine ⟨fun σ i v => ?_, ih.2⟩
    have := ih.1 σ i v
    simp only [polSat, if_true, Tr.sat] at this ⊢
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨(this.1 ⟨h1, h2⟩).1, (this.1 ⟨h1, h2⟩).2, h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨(this.2 ⟨h1, h2⟩).1, (this.2 ⟨h1, h2⟩).2, h3⟩
  | andR _ ih =>
    refine ⟨fun σ i v => ?_, ih.2⟩
    have := ih.1 σ i v
    simp only [polSat, if_true, Tr.sat] at this ⊢
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨(this.1 ⟨h1, h3⟩).1, h2, (this.1 ⟨h1, h3⟩).2⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨(this.2 ⟨h1, h3⟩).1, h2, (this.2 ⟨h1, h3⟩).2⟩
  | andNeg _ _ ih1 ih2 =>
    refine ⟨fun σ i v => ?_, ?_⟩
    · have h1 := ih1.1 σ i v
      have h2 := ih2.1 σ i v
      simp only [polSat, Bool.false_eq_true, if_false, Tr.sat, impFm, Tr.sat_disj,
        Guards.sat_toFm, Guards.sat_append] at h1 h2 ⊢
      exact andNeg_prop h1 h2
    · intro κ hκ
      rcases List.mem_append.1 hκ with h | h
      · exact ih1.2 κ h
      · exact ih2.2 κ h

end GX

namespace GX
variable {m : Pr B L → Prop} {x : ℕ}

/-- Every resulting guard extends some original guard. -/
theorem extends_ {p : Bool} {π π' : Guards B L D} {φ φ' : Fm B L D} (h : GX m x p π φ π' φ') :
    ∀ κ' ∈ π', ∃ κ ∈ π, ∀ a ∈ κ, a ∈ κ' := by
  induction h with
  | grd => intro κ hκ; exact ⟨κ, hκ, fun _ h => h⟩
  | vacPos | vacNeg => intro κ hκ; simp at hκ
  | pred | eq =>
    intro κ' hκ'
    obtain ⟨κ, hκ, rfl⟩ := List.mem_map.1 hκ'
    exact ⟨κ, hκ, fun a ha => List.mem_append_left _ ha⟩
  | neg _ ih | andL _ ih | andR _ ih => exact ih
  | andNeg _ _ ih1 ih2 =>
    intro κ hκ
    rcases List.mem_append.1 hκ with h | h
    · exact ih1 κ h
    · exact ih2 κ h

theorem bindsAll_preserved {p : Bool} {π π' : Guards B L D} {φ φ' : Fm B L D} (h : GX m x p π φ π' φ') {y : ℕ}
    (hy : Guards.bindsAll y π) : Guards.bindsAll y π' := by
  intro κ' hκ'
  obtain ⟨κ, hκ, hsub⟩ := h.extends_ κ' hκ'
  obtain ⟨a, ha, hb⟩ := hy κ hκ
  exact ⟨a, hsub a ha, hb⟩

end GX

/-- The paper's `Guards^m_X(Φ)`: guard extraction iterated over the variables
    `X`, starting from the trivial guard `⊤`. -/
inductive GXs (m : Pr B L → Prop) :
    List ℕ → Guards B L D → Fm B L D → Guards B L D → Fm B L D → Prop
  | nil {π φ} : GXs m [] π φ π φ
  | cons {x xs π φ π₁ φ₁ π' φ'} : GX m x true π φ π₁ φ₁ → GXs m xs π₁ φ₁ π' φ' →
      GXs m (x :: xs) π φ π' φ'

/-- The original sequential `Guards` (superseded by `GXJ`, Lemma 4.3): if `Guards^m_X(Φ) = (π, φ)` then `π ∧ φ ≡ Φ` and every
    variable of `X` is bound in every disjunct of `π`. -/
theorem GXs.preserve {m : Pr B L → Prop} {xs π φ π' φ'} (h : GXs m xs π φ π' φ') {y : ℕ}
    (hy : Guards.bindsAll y π) : Guards.bindsAll (B := B) (L := L) (D := D) y π' := by
  induction h with
  | nil => exact hy
  | cons h₁ _ ih => exact ih (h₁.bindsAll_preserved hy)

theorem GXs.sound {m : Pr B L → Prop} {xs} {π π' : Guards B L D} {φ φ' : Fm B L D} (h : GXs m xs π φ π' φ') :
    GEquiv true π φ π' φ' ∧ ∀ x ∈ xs, π'.bindsAll x := by
  induction h with
  | nil => exact ⟨fun _ _ _ => Iff.rfl, by simp⟩
  | cons h₁ hrest ih =>
    refine ⟨fun σ i v => (h₁.sound.1 σ i v).trans (ih.1 σ i v), ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hrest.preserve h₁.sound.2
    · exact ih.2 y hy

end Enfflash
