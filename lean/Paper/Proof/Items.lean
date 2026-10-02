/-
  The items of the compiled program.
-/
import Paper.Proof.Program

namespace Paper

open Classical

variable {Voc : Vocabulary}

section
variable (Ξ : RwSetting Voc) (Γ : LetCtx Voc) (colTy : Voc.𝕍 → Ty) (d : LetDef Voc)

/-- The enumerable events `m = m_Γ` of `letItem`. -/
def letM : Set Voc.ℰ := Ξ.m Γ

/-- The columns of `letItem`. -/
def letCols : List (Col Voc) := d.xs.map fun x => (⟨x, colTy x⟩ : Col Voc)

/-- A compiled trigger: `Guards^m_X(Φ) = (π, ψ)` and `toClause π ψ = cl`. -/
def GuardClause (m : Set Voc.ℰ) (X : Set Voc.𝕍) (Φ : Formula Voc) (cl : Clause Voc) : Prop :=
  ∃ π ψ, Guards m X Φ = some (π, ψ) ∧ toClause π ψ = some cl

/-- The items realizing a let body. -/
inductive LetItemSpec : Item Voc → Prop
  | once (I : Interval) (φ : Formula Voc) (a : Clause Voc) :
      stripExists d.φ = .since I .top φ → GuardClause (letM Ξ Γ) φ.fv φ a →
      LetItemSpec (.table none false d.e (letCols colTy d) (some I.bounds) a none)
  | prev (I : Interval) (φ : Formula Voc) (a : Clause Voc) :
      stripExists d.φ = .prev I φ → GuardClause (letM Ξ Γ) φ.fv φ a →
      LetItemSpec (.table none true d.e (letCols colTy d) (some I.bounds) a none)
  | agg (ys : List Voc.𝕍) (ω : Voc.Ω) (ss : List (Term Voc)) (gs : List Voc.𝕍) (φ : Formula Voc)
      (a : Clause Voc) :
      stripExists d.φ = .agg ys ω ss gs φ → d.xs = gs ++ ys → (gs ++ ys).Nodup →
      GuardClause (letM Ξ Γ) φ.fv φ a →
      LetItemSpec (.agg none d.e (letCols colTy d) ω ss gs a)
  | since (I : Interval) (φl φr : Formula Voc) (a r : Clause Voc) :
      stripExists d.φ = .since I φl φr → φl ≠ .top →
      GuardClause (letM Ξ Γ) ({x | x ∈ d.xs} ∪ (stripExists d.φ).fv) φr a →
      GuardClause (letM Ξ Γ) ({x | x ∈ d.xs} ∪ (stripExists d.φ).fv) (.neg φl) r →
      LetItemSpec (.table none false d.e (letCols colTy d) (some I.bounds) a (some r))
  | filt (f : Filter Voc) :
      (∀ I φl φr, stripExists d.φ ≠ .since I φl φr) → (∀ I φ, stripExists d.φ ≠ .prev I φ) →
      (∀ ys ω ss gs φ, stripExists d.φ ≠ .agg ys ω ss gs φ) →
      (∃ c s, Γ d.e = some (false, c, s)) → (stripExists d.φ).toFilter = some f →
      LetItemSpec (.let_ none true d.e (letCols colTy d) (.filter f))
  | plet (a : Clause Voc) :
      (∀ I φl φr, stripExists d.φ ≠ .since I φl φr) → (∀ I φ, stripExists d.φ ≠ .prev I φ) →
      (∀ ys ω ss gs φ, stripExists d.φ ≠ .agg ys ω ss gs φ) →
      (∀ c s, Γ d.e ≠ some (false, c, s)) →
      GuardClause (letM Ξ Γ) ({x | x ∈ d.xs} ∪ (stripExists d.φ).fv) (stripExists d.φ) a →
      LetItemSpec (.let_ none false d.e (letCols colTy d) a)

theorem cl_some {m : Set Voc.ℰ} {X : Set Voc.𝕍} {Φ : Formula Voc} {a : Clause Voc}
    (h : ∃ θ, Guards m X Φ = some θ ∧ toClause θ.1 θ.2 = some a) : GuardClause m X Φ a := by
  obtain ⟨θ, h1, h2⟩ := h
  exact ⟨θ.1, θ.2, h1, h2⟩

theorem letItem_spec {it : Item Voc} (h : letItem Ξ Γ colTy d = some it) : LetItemSpec Ξ Γ colTy d it := by
  unfold letItem at h
  generalize hχ : stripExists d.φ = χ at h
  cases χ with
  | since I φl φr =>
    cases φl with
    | top =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨a, ha, rfl⟩ := h
      exact .once I _ a hχ (cl_some ha)
    | _ =>
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨a, ha, r, hr, rfl⟩ := h
      exact .since I _ φr a r hχ (by simp) (by rw [hχ]; exact cl_some ha)
        (by rw [hχ]; exact cl_some hr)
  | prev I φ =>
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact .prev I φ a hχ (cl_some ha)
  | agg ys ω ss gs φ =>
    simp only at h
    split_ifs at h with hc
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    exact .agg ys ω ss gs φ a hχ hc.1 hc.2 (cl_some ha)
  | _ =>
    simp only at h
    cases hΓ : Γ d.e with
    | none =>
      rw [hΓ] at h
      simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
      obtain ⟨a, ha, rfl⟩ := h
      exact .plet a (by simp [hχ]) (by simp [hχ]) (by simp [hχ]) (by simp [hΓ])
        (by rw [hχ]; exact cl_some ha)
    | some t =>
      obtain ⟨g, c, s⟩ := t
      rw [hΓ] at h
      cases g with
      | false =>
        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
        obtain ⟨f, hf, rfl⟩ := h
        exact .filt f (by simp [hχ]) (by simp [hχ]) (by simp [hχ]) ⟨c, s, hΓ⟩ (by rw [hχ]; exact hf)
      | true =>
        simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
        obtain ⟨a, ha, rfl⟩ := h
        exact .plet a (by simp [hχ]) (by simp [hχ]) (by simp [hχ]) (by simp [hΓ])
          (by rw [hχ]; exact cl_some ha)

theorem LetItemSpec.defName {it : Item Voc} (h : LetItemSpec Ξ Γ colTy d it) :
    it.defName? = some d.e ∧ ¬ it.isRule ∧ ∀ k, it ≠ .sec k := by
  cases h <;> simp [Item.defName?, Item.isRule]

end

end Paper
