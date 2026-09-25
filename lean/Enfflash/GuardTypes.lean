/-
  Enfflash formalization — declarative guardedness (the `GRD` judgments of
  the type system, Appendix "A type system for the enforceable fragment").

  * `Grd m x p φ`: variable `x` is guarded in `pφ` (for polarity `p`), i.e.
    its values satisfying `pφ` can be enumerated from the enumerable
    predicates `m`.
  * `gx_iff`: guard extraction `↝` (Figure 4) succeeds on a trigger `(π, φ)`
    iff `π` already binds `x` in every disjunct, or `x` is guarded in `φ`.
  * `GXJ`: joint guard extraction for a set of variables (Figure 5, the
    paper's `Guards^m_X`), with `GXJ.sound` and `gxj_iff`: it succeeds iff every variable
    is guarded, i.e. iff the formula is enumerable (`Enum`).

  The sequential extraction `GXs` (the paper's original `Guards`) is
  order-dependent and incomplete: for `A(x,y) ∨ (C(y) ∧ D(x))` every variable
  is guarded, but extracting `x` then `y` (or `y` then `x`) fails.
-/
import Enfflash.Guards

namespace Enfflash

universe u
variable {B L D : Type u}

/-- Per-variable guardedness. -/
inductive Grd (m : Pr B L → Prop) (x : ℕ) : Bool → Fm B L D → Prop
  | pred {p ts} : m p → Term.var x ∈ ts → Grd m x true (.pred p ts)
  | eq {d} : Grd m x true (.eq (.var x) (.const d))
  | top : Grd m x false .tt
  | neg {p φ} : Grd m x (!p) φ → Grd m x p (.neg φ)
  | andL {φ ψ} : Grd m x true φ → Grd m x true (.conj φ ψ)
  | andR {φ ψ} : Grd m x true ψ → Grd m x true (.conj φ ψ)
  | andNeg {φ ψ} : Grd m x false φ → Grd m x false ψ → Grd m x false (.conj φ ψ)

/-- A formula is enumerable w.r.t. the variables `X` (in polarity `p`). -/
def Enum (m : Pr B L → Prop) (X : List ℕ) (p : Bool) (φ : Fm B L D) : Prop :=
  ∀ x ∈ X, Grd m x p φ

/-- **Guard extraction, declaratively.**  Extraction for `x` succeeds on
    `(π, φ)` iff every disjunct of `π` binds `x` or `x` is guarded in `φ`. -/
theorem gx_iff {m : Pr B L → Prop} {x : ℕ} {p : Bool} {π : Guards B L D} {φ : Fm B L D} :
    (∃ π' φ', GX m x p π φ π' φ') ↔ (π.bindsAll x ∨ Grd m x p φ) := by
  constructor
  · rintro ⟨π', φ', h⟩
    induction h with
    | grd hb => exact Or.inl hb
    | vacPos => exact Or.inr (.neg .top)
    | vacNeg => exact Or.inr .top
    | pred hm hx => exact Or.inr (.pred hm hx)
    | eq => exact Or.inr .eq
    | neg _ ih =>
      rcases ih with h | h
      · exact Or.inl h
      · exact Or.inr (.neg h)
    | andL _ ih => exact ih.imp id .andL
    | andR _ ih => exact ih.imp id .andR
    | andNeg _ _ ih₁ ih₂ =>
      rcases ih₁ with h | h
      · exact Or.inl h
      rcases ih₂ with h' | h'
      · exact Or.inl h'
      · exact Or.inr (.andNeg h h')
  · rintro (h | h)
    · exact ⟨π, φ, .grd h⟩
    · induction h with
      | pred hm hx => exact ⟨_, _, .pred hm hx⟩
      | eq => exact ⟨_, _, .eq⟩
      | top => exact ⟨_, _, .vacNeg⟩
      | neg _ ih => obtain ⟨π', φ', h⟩ := ih; exact ⟨_, _, .neg h⟩
      | andL _ ih => obtain ⟨π', φ', h⟩ := ih; exact ⟨_, _, .andL h⟩
      | andR _ ih => obtain ⟨π', φ', h⟩ := ih; exact ⟨_, _, .andR h⟩
      | andNeg _ _ ih₁ ih₂ =>
        obtain ⟨π₁, φ₁, h₁⟩ := ih₁; obtain ⟨π₂, φ₂, h₂⟩ := ih₂; exact ⟨_, _, .andNeg h₁ h₂⟩

/-! ## Joint guard extraction -/

/-- Conjunction of two disjunctions of guards. -/
def Guards.prod (π₁ π₂ : Guards B L D) : Guards B L D :=
  π₁.flatMap fun κ₁ => π₂.map fun κ₂ => κ₁ ++ κ₂

theorem Guards.sat_prod (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (π₁ π₂ : Guards B L D) :
    (Guards.prod π₁ π₂).sat σ i v ↔ π₁.sat σ i v ∧ π₂.sat σ i v := by
  simp only [Guards.sat, Guards.prod, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨κ₁, h₁, κ₂, h₂, rfl⟩, hall⟩
    exact ⟨⟨κ₁, h₁, fun a ha => hall a (List.mem_append_left _ ha)⟩,
      ⟨κ₂, h₂, fun a ha => hall a (List.mem_append_right _ ha)⟩⟩
  · rintro ⟨⟨κ₁, h₁, a₁⟩, ⟨κ₂, h₂, a₂⟩⟩
    exact ⟨_, ⟨κ₁, h₁, κ₂, h₂, rfl⟩, fun a ha =>
      (List.mem_append.1 ha).elim (a₁ a) (a₂ a)⟩

/-- Joint guard extraction for the variables `X` from `(⊤, φ)`: the corrected
    `Guards^m_X(φ)`. -/
inductive GXJ (m : Pr B L → Prop) : List ℕ → Bool → Fm B L D → Guards B L D → Fm B L D → Prop
  | none {p φ} : GXJ m [] p φ [[]] φ
  | vac {X} : GXJ m X false .tt [] .tt
  | pred {X p ts} : m p → (∀ x ∈ X, Term.var x ∈ ts) →
      GXJ m X true (.pred p ts) [[.pred p ts]] .tt
  | eq {X y d} : (∀ x ∈ X, x = y) →
      GXJ m X true (.eq (.var y) (.const d)) [[.eq (.var y) d]] .tt
  | neg {X p φ π φ'} : GXJ m X (!p) φ π φ' → GXJ m X p (.neg φ) π (.neg φ')
  | andPos {X X₁ X₂ φ ψ π₁ φ₁ π₂ ψ₂} : GXJ m X₁ true φ π₁ φ₁ → GXJ m X₂ true ψ π₂ ψ₂ →
      (∀ x ∈ X, x ∈ X₁ ∨ x ∈ X₂) →
      GXJ m X true (.conj φ ψ) (Guards.prod π₁ π₂) (.conj φ₁ ψ₂)
  | andNeg {X φ ψ π₁ φ₁ π₂ ψ₂} : GXJ m X false φ π₁ φ₁ → GXJ m X false ψ π₂ ψ₂ →
      GXJ m X false (.conj φ ψ) (π₁ ++ π₂) (.conj (impFm π₁ φ₁) (impFm π₂ ψ₂))

private theorem andNeg_prop' {F G P₁ F₁ P₂ G₂ : Prop}
    (h1 : ¬F ↔ P₁ ∧ ¬F₁) (h2 : ¬G ↔ P₂ ∧ ¬G₂) :
    ¬(F ∧ G) ↔ ((P₁ ∨ P₂) ∧ ¬((¬P₁ ∨ F₁) ∧ (¬P₂ ∨ G₂))) := by
  by_cases hF : F <;> by_cases hG : G <;>
    by_cases hP₁ : P₁ <;> by_cases hF₁ : F₁ <;> by_cases hP₂ : P₂ <;> by_cases hG₂ : G₂ <;>
    simp_all

/-- **Lemma 4.3** (joint guard extraction is sound): the resulting trigger is equivalent,
    and every disjunct binds every variable of `X`. -/
theorem GXJ.sound {m : Pr B L → Prop} {X : List ℕ} {p : Bool} {φ φ' : Fm B L D}
    {π : Guards B L D} (h : GXJ m X p φ π φ') :
    GEquiv p [[]] φ π φ' ∧ ∀ x ∈ X, π.bindsAll x := by
  induction h with
  | none => exact ⟨fun _ _ _ => Iff.rfl, by simp⟩
  | vac => exact ⟨fun σ i v => by simp [polSat, Tr.sat, Guards.sat], by simp [Guards.bindsAll]⟩
  | pred _ hx =>
    refine ⟨fun σ i v => ?_, fun x hx' κ hκ => ?_⟩
    · simp [polSat, Guards.sat, Tr.sat, GAtom.sat]
    · simp only [List.mem_singleton] at hκ; subst hκ
      exact ⟨_, List.mem_singleton_self _, hx x hx'⟩
  | eq hx =>
    refine ⟨fun σ i v => ?_, fun x hx' κ hκ => ?_⟩
    · simp [polSat, Guards.sat, Tr.sat, GAtom.sat, Term.eval]
    · simp only [List.mem_singleton] at hκ; subst hκ
      exact ⟨_, List.mem_singleton_self _, by simp [GAtom.binds, hx x hx']⟩
  | @neg X p φ π φ' _ ih =>
    refine ⟨fun σ i v => ?_, ih.2⟩
    have := ih.1 σ i v
    cases p <;> simp_all [polSat, Tr.sat]
  | andPos _ _ hX ih₁ ih₂ =>
    refine ⟨fun σ i v => ?_, fun x hx κ hκ => ?_⟩
    · have h1 := ih₁.1 σ i v
      have h2 := ih₂.1 σ i v
      have ht : Guards.sat σ i v ([[]] : Guards B L D) := Guards.sat_top σ i v
      simp only [polSat, if_true, Tr.sat, Guards.sat_prod, ht, true_and] at h1 h2 ⊢
      rw [h1, h2]; tauto
    · simp only [Guards.prod, List.mem_flatMap, List.mem_map] at hκ
      obtain ⟨κ₁, h₁, κ₂, h₂, rfl⟩ := hκ
      rcases hX x hx with h | h
      · obtain ⟨a, ha, hb⟩ := ih₁.2 x h κ₁ h₁; exact ⟨a, List.mem_append_left _ ha, hb⟩
      · obtain ⟨a, ha, hb⟩ := ih₂.2 x h κ₂ h₂; exact ⟨a, List.mem_append_right _ ha, hb⟩
  | andNeg _ _ ih₁ ih₂ =>
    refine ⟨fun σ i v => ?_, fun x hx κ hκ => ?_⟩
    · have h1 := ih₁.1 σ i v
      have h2 := ih₂.1 σ i v
      have ht : Guards.sat σ i v ([[]] : Guards B L D) := Guards.sat_top σ i v
      simp only [polSat, Bool.false_eq_true, if_false, Tr.sat, impFm, Tr.sat_disj,
        Guards.sat_toFm, Guards.sat_append, ht, true_and] at h1 h2 ⊢
      exact andNeg_prop' h1 h2
    · rcases List.mem_append.1 hκ with h | h
      exacts [ih₁.2 x hx κ h, ih₂.2 x hx κ h]

/-- **Joint extraction succeeds iff the formula is enumerable.** -/
theorem gxj_iff {m : Pr B L → Prop} {X : List ℕ} {p : Bool} {φ : Fm B L D} :
    (∃ π φ', GXJ m X p φ π φ') ↔ Enum m X p φ := by
  constructor
  · rintro ⟨π, φ', h⟩
    induction h with
    | none => intro x hx; simp at hx
    | vac => exact fun _ _ => .top
    | pred hm hx => exact fun x h => .pred hm (hx x h)
    | eq hx => intro x h; rw [hx x h]; exact .eq
    | neg _ ih => exact fun x h => .neg (ih x h)
    | andPos _ _ hX ih₁ ih₂ =>
      intro x h
      rcases hX x h with h | h
      exacts [.andL (ih₁ x h), .andR (ih₂ x h)]
    | andNeg _ _ ih₁ ih₂ => exact fun x h => .andNeg (ih₁ x h) (ih₂ x h)
  · intro h
    induction φ generalizing X p with
    | tt =>
      cases X with
      | nil => exact ⟨_, _, .none⟩
      | cons x X =>
        cases p with
        | false => exact ⟨_, _, .vac⟩
        | true => cases h x (List.mem_cons_self ..)
    | pred q ts =>
      cases X with
      | nil => exact ⟨_, _, .none⟩
      | cons x X =>
        cases p with
        | false => cases h x (List.mem_cons_self ..)
        | true =>
          have hm : m q := by cases h x (List.mem_cons_self ..) with | pred hm _ => exact hm
          exact ⟨_, _, .pred hm fun y hy => by cases h y hy with | pred _ hx => exact hx⟩
    | eq t u =>
      cases X with
      | nil => exact ⟨_, _, .none⟩
      | cons x X =>
        cases p with
        | false => cases h x (List.mem_cons_self ..)
        | true =>
          have hx := h x (List.mem_cons_self ..)
          cases hx with
          | eq =>
            exact ⟨_, _, .eq fun y hy => by cases h y hy with | eq => rfl⟩
    | neg φ ih =>
      obtain ⟨π, φ', hj⟩ := ih (X := X) (p := !p) fun x hx => by
        cases h x hx with | neg hg => exact hg
      exact ⟨_, _, .neg hj⟩
    | conj φ ψ ih₁ ih₂ =>
      cases X with
      | nil => exact ⟨_, _, .none⟩
      | cons x X =>
      cases p with
      | true =>
        -- split the variables by the conjunct guarding them
        classical
        let X₁ := (x :: X).filter fun y => decide (Grd m y true φ)
        let X₂ := (x :: X).filter fun y => ¬ decide (Grd m y true φ)
        obtain ⟨π₁, φ₁, h₁⟩ := ih₁ (X := X₁) (p := true) fun y hy => by
          simp only [X₁, List.mem_filter, decide_eq_true_eq] at hy; exact hy.2
        obtain ⟨π₂, ψ₂, h₂⟩ := ih₂ (X := X₂) (p := true) fun y hy => by
          simp only [X₂, List.mem_filter, decide_eq_true_eq, decide_not] at hy
          cases h y hy.1 with
          | andL hg => exact absurd hg (by simpa using hy.2)
          | andR hg => exact hg
        refine ⟨_, _, .andPos h₁ h₂ fun y hy => ?_⟩
        by_cases hg : Grd m y true φ
        · exact Or.inl (by simp [X₁, hy, hg])
        · exact Or.inr (by simp [X₂, hy, hg])
      | false =>
        obtain ⟨π₁, φ₁, h₁⟩ := ih₁ (X := x :: X) (p := false) fun y hy => by
          cases h y hy with | andNeg hg _ => exact hg
        obtain ⟨π₂, ψ₂, h₂⟩ := ih₂ (X := x :: X) (p := false) fun y hy => by
          cases h y hy with | andNeg _ hg => exact hg
        exact ⟨_, _, .andNeg h₁ h₂⟩
    | ex φ _ =>
      cases X with
      | nil => exact ⟨_, _, .none⟩
      | cons x X => cases h x (List.mem_cons_self ..)
    | ev a b φ _ =>
      cases X with
      | nil => exact ⟨_, _, .none⟩
      | cons x X => cases h x (List.mem_cons_self ..)
    | nx a b φ _ =>
      cases X with
      | nil => exact ⟨_, _, .none⟩
      | cons x X => cases h x (List.mem_cons_self ..)

end Enfflash
