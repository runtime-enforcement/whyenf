/-
  Basic formulas and past locality.
-/
import Paper.Proof.Setup

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-- Built from `⊤`, atoms, equations, `¬` and `∧`. -/
def Formula.Basic : Formula Voc → Prop
  | .top | .pred _ _ | .eq _ _ => True
  | .neg φ => φ.Basic
  | .and φ ψ => φ.Basic ∧ ψ.Basic
  | _ => False

theorem toFilter_basic : ∀ {φ : Formula Voc} {f : Filter Voc}, φ.toFilter = some f → φ.Basic
  | .top, _, _ | .pred .., _, _ => trivial
  | .neg φ, f, h => by
    simp only [Formula.toFilter, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨f', hf', -⟩ := h; exact toFilter_basic (φ := φ) hf'
  | .and φ ψ, f, h => by
    simp only [Formula.toFilter] at h
    cases h₁ : φ.toFilter <;> cases h₂ : ψ.toFilter <;>
      simp [h₁, h₂, Seq.seq, Option.map_eq_map] at h
    exact ⟨toFilter_basic h₁, toFilter_basic h₂⟩
  | .ex .., _, h | .next .., _, h | .prev .., _, h | .eventually .., _, h | .since .., _, h
  | .letin .., _, h | .agg .., _, h | .eq .., _, h => by simp [Formula.toFilter] at h

theorem toFilter_imp_basic {φ ψ : Formula Voc} {f : Filter Voc} (h : (Formula.imp φ ψ).toFilter = some f) :
    ψ.Basic := by
  have := toFilter_basic h
  simp only [Formula.imp, Formula.or, Formula.Basic] at this
  exact this.2

theorem toFilter_and {φ ψ : Formula Voc} {f : Filter Voc} (h : (Formula.and φ ψ).toFilter = some f) :
    ∃ fa fb, φ.toFilter = some fa ∧ ψ.toFilter = some fb := by
  simp only [Formula.toFilter] at h
  cases h₁ : φ.toFilter <;> cases h₂ : ψ.toFilter <;> simp [h₁, h₂, Seq.seq, Option.map_eq_map] at h
  exact ⟨_, _, rfl, rfl⟩

theorem toFilter_neg {φ : Formula Voc} {f : Filter Voc} (h : (Formula.neg φ).toFilter = some f) :
    ∃ f', φ.toFilter = some f' := by
  simp only [Formula.toFilter, Option.map_eq_map, Option.map_eq_some_iff] at h
  obtain ⟨f', hf', -⟩ := h; exact ⟨f', hf'⟩

theorem toFilter_imp {φ ψ : Formula Voc} {f : Filter Voc} (h : (Formula.imp φ ψ).toFilter = some f) :
    ∃ f', ψ.toFilter = some f' := by
  simp only [Formula.imp, Formula.or] at h
  obtain ⟨f₁, hf₁⟩ := toFilter_neg h
  obtain ⟨-, fb, -, hb⟩ := toFilter_and hf₁
  exact toFilter_neg hb

theorem GX.basic {m : Set Voc.ℰ} {p X Φ π φ} (h : GX m p X Φ π φ) :
    ∀ f : Filter Voc, φ.toFilter = some f → Φ.Basic := by
  induction h with
  | none => exact fun f hf => toFilter_basic hf
  | vac => exact fun _ _ => trivial
  | pred => exact fun _ _ => trivial
  | eq => exact fun _ _ => trivial
  | andPos _ _ _ ih₁ ih₂ =>
    intro f hf
    obtain ⟨fa, fb, ha, hb⟩ := toFilter_and hf
    exact ⟨ih₁ fa ha, ih₂ fb hb⟩
  | andNeg _ _ ih₁ ih₂ =>
    intro f hf
    obtain ⟨fa, fb, ha, hb⟩ := toFilter_and hf
    obtain ⟨fa', ha'⟩ := toFilter_imp ha
    obtain ⟨fb', hb'⟩ := toFilter_imp hb
    exact ⟨ih₁ fa' ha', ih₂ fb' hb'⟩
  | neg _ ih =>
    intro f hf
    obtain ⟨f', hf'⟩ := toFilter_neg hf
    exact ih f' hf'

theorem toClause_filter {π : GDisj Voc} {ψ : Formula Voc} {cl : Clause Voc}
    (h : toClause π ψ = some cl) : ∃ f, ψ.toFilter = some f := by
  unfold toClause at h
  split at h
  · simp only [Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨f, hf, -⟩ := h; exact ⟨f, hf⟩
  · simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨g, -, f, hf, -⟩ := h; exact ⟨f, hf⟩

theorem GuardClause.basic {m : Set Voc.ℰ} {X : Set Voc.𝕍} {Φ : Formula Voc} {cl : Clause Voc}
    (h : GuardClause m X Φ cl) : Φ.Basic := by
  obtain ⟨π, ψ, hg, hc⟩ := h
  obtain ⟨f, hf⟩ := toClause_filter hc
  exact (Guards_spec hg).basic f hf

/-! ## Basic formulas only look at the current time-point -/

theorem Formula.Basic.sat_congr {φ : Formula Voc} (h : φ.Basic) {S S' : Str Voc.toSignature}
    {i i' : ℕ} (hD : S.D i = S'.D i') (v : Val Voc) : φ.sat S v i ↔ φ.sat S' v i' := by
  induction φ with
  | top => rfl
  | pred e ts => simp only [Formula.sat, hD]
  | eq x c => rfl
  | neg φ ih => simp only [Formula.sat]; rw [ih h]
  | and φ ψ ih₁ ih₂ => simp only [Formula.sat]; rw [ih₁ h.1, ih₂ h.2]
  | _ => exact h.elim

/-! ## Past formulas only look at the past -/

/-- No future operator and no `let`. -/
def Formula.PastF : Formula Voc → Prop
  | .top | .pred _ _ | .eq _ _ => True
  | .neg φ | .ex _ φ | .prev _ φ | .agg _ _ _ _ φ => φ.PastF
  | .and φ ψ | .since _ φ ψ => φ.PastF ∧ ψ.PastF
  | _ => False

theorem Formula.Basic.pastF : ∀ {φ : Formula Voc}, φ.Basic → φ.PastF
  | .top, _ | .pred .., _ | .eq .., _ => trivial
  | .neg φ, h => Formula.Basic.pastF (φ := φ) h
  | .and φ ψ, h => ⟨Formula.Basic.pastF h.1, Formula.Basic.pastF h.2⟩
  | .ex .., h | .next .., h | .prev .., h | .eventually .., h | .since .., h | .letin .., h
  | .agg .., h => h.elim

theorem exs_pastF (ys : List Voc.𝕍) {χ : Formula Voc} (h : χ.PastF) : (Formula.exs ys χ).PastF := by
  induction ys with
  | nil => exact h
  | cons y ys ih => exact ih

theorem exs_stripExists : ∀ φ : Formula Voc, ∃ ys, φ = Formula.exs ys (stripExists φ)
  | .ex x φ => by
    obtain ⟨ys, h⟩ := exs_stripExists φ
    exact ⟨x :: ys, by simp only [stripExists, Formula.exs, List.foldr_cons]; rw [← Formula.exs, ← h]⟩
  | .top | .pred .. | .eq .. | .neg _ | .and .. | .next .. | .prev .. | .eventually .. | .since ..
  | .letin .. | .agg .. => ⟨[], rfl⟩

theorem letBody_prev {ψ φ : Formula Voc} {I : Interval} (hb : ψ.IsLetBody)
    (h : stripExists ψ = .prev I φ) : ψ = .prev I φ := by
  rcases hb with ⟨ys, χ, rfl, hχ⟩ | ⟨I', ψ', rfl, -⟩ | ⟨I', l, r, rfl, -⟩ | ⟨ys, ω, ss, gs, ψ', rfl, -⟩
  · rw [stripExists_exs] at h; exact absurd h ((IsChi_stripExists hχ).2.1 _ _)
  · simpa [stripExists] using h
  · simp [stripExists] at h
  · simp [stripExists] at h

theorem letBody_agg {ψ φ : Formula Voc} {ys : List Voc.𝕍} {ω : Voc.Ω} {ss : List (Term Voc)}
    {gs : List Voc.𝕍} (hb : ψ.IsLetBody) (h : stripExists ψ = .agg ys ω ss gs φ) :
    ψ = .agg ys ω ss gs φ := by
  rcases hb with ⟨ys', χ, rfl, hχ⟩ | ⟨I', ψ', rfl, -⟩ | ⟨I', l, r, rfl, -⟩ | ⟨ys', ω', ss', gs', ψ', rfl, -⟩
  · rw [stripExists_exs] at h; exact absurd h ((IsChi_stripExists hχ).2.2 _ _ _ _ _)
  · simp [stripExists] at h
  · simp [stripExists] at h
  · simpa [stripExists] using h

/-- Two structures agree up to time-point `m`. -/
def PastAgree (S₁ S₂ : Str Voc.toSignature) (m : ℕ) : Prop :=
  ∀ k ≤ m, S₁.τ k = S₂.τ k ∧ S₁.D k = S₂.D k

theorem Formula.PastF.sat_congr {φ : Formula Voc} (h : φ.PastF) {S₁ S₂ : Str Voc.toSignature} {m : ℕ}
    (hA : PastAgree S₁ S₂ m) : ∀ i ≤ m, ∀ v, φ.sat S₁ v i ↔ φ.sat S₂ v i := by
  induction φ with
  | top => intros; rfl
  | pred e ts => intro i hi v; simp only [Formula.sat, (hA i hi).2]
  | eq x c => intros; rfl
  | neg φ ih => intro i hi v; simp only [Formula.sat]; rw [ih h i hi v]
  | and φ ψ ih₁ ih₂ => intro i hi v; simp only [Formula.sat]; rw [ih₁ h.1 i hi v, ih₂ h.2 i hi v]
  | ex x φ ih => intro i hi v; simp only [Formula.sat]; exact exists_congr fun d => ih h i hi _
  | prev I φ ih =>
    intro i hi v; simp only [Formula.sat]
    by_cases hi0 : i > 0
    · rw [ih h (i - 1) (by omega) v, (hA i hi).1, (hA (i - 1) (by omega)).1]
    · simp [hi0]
  | since I φ ψ ih₁ ih₂ =>
    intro i hi v; simp only [Formula.sat]
    refine exists_congr fun j => ?_
    constructor
    · rintro ⟨hj, hI, hψ, hφ⟩
      refine ⟨hj, by rwa [← (hA i hi).1, ← (hA j (by omega)).1], (ih₂ h.2 j (by omega) v).1 hψ,
        fun k h1 h2 => (ih₁ h.1 k (by omega) v).1 (hφ k h1 h2)⟩
    · rintro ⟨hj, hI, hψ, hφ⟩
      refine ⟨hj, by rwa [(hA i hi).1, (hA j (by omega)).1], (ih₂ h.2 j (by omega) v).2 hψ,
        fun k h1 h2 => (ih₁ h.1 k (by omega) v).2 (hφ k h1 h2)⟩
  | agg ys ω ss gs φ ih =>
    intro i hi v
    simp only [Formula.sat]
    have e : {v' : Val Voc | (∀ x, (v' x).isSome ↔ x ∈ φ.fv) ∧ gs.map v' = gs.map v ∧ φ.sat S₁ v' i} =
        {v' : Val Voc | (∀ x, (v' x).isSome ↔ x ∈ φ.fv) ∧ gs.map v' = gs.map v ∧ φ.sat S₂ v' i} := by
      ext v'; simp only [Set.mem_setOf_eq, ih h i hi v']
    rw [e]
  | next | eventually | letin => exact h.elim

theorem applyLets_past (ℒ : List (LetDef Voc)) (hℒ : ∀ d ∈ ℒ, d.φ.PastF) :
    ∀ {S₁ S₂ : Str Voc.toSignature} {m : ℕ}, PastAgree S₁ S₂ m →
      PastAgree (applyLets ℒ S₁) (applyLets ℒ S₂) m := by
  induction ℒ with
  | nil => intro S₁ S₂ m h; exact h
  | cons d ℒ ih =>
    intro S₁ S₂ m h
    simp only [applyLets, List.foldl_cons]
    rw [← applyLets, ← applyLets]
    refine ih (fun d' hd' => hℒ d' (by simp [hd'])) ?_
    intro k hk
    refine ⟨(h k hk).1, ?_⟩
    simp only [Str.extend, (h k hk).2]
    ext ev
    simp only [Set.mem_union, Set.mem_setOf_eq]
    refine or_congr_right (and_congr_right fun _ => exists_congr fun v' =>
      and_congr_right fun _ => and_congr_right fun _ => ?_)
    exact (hℒ d (by simp)).sat_congr h k hk v'

end Paper
