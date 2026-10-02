/-
  One time-point: `Saturate` on the compiled program.
-/
import Paper.Proof.Local

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem Decomp.base_end {ℒ : List (LetDef Voc)} {q e : Voc.ℰ} (h : Decomp ℒ q e) : ¬ IsLet ℒ e := by
  induction h with
  | base h => exact h
  | let_ _ _ _ ih => exact ih

theorem names_basic {φ : Formula Voc} (h : φ.Basic) : φ.names = φ.preds :=
  Formula.names_eq_preds (by
    induction φ with
    | top | pred | eq => trivial
    | neg φ ih => exact ih h
    | and φ ψ ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
    | _ => exact h.elim)

theorem conj_basic (κ : GConj Voc) : κ.toFormula.Basic := by
  induction κ with
  | nil => trivial
  | cons γ κ ih => refine ⟨?_, ih⟩; cases γ <;> trivial

/-- The trigger semantics only depends on the trigger's events. -/
theorem trigSem_congr {S S' : Str Voc.toSignature} {N : Set Voc.ℰ} (h : S.Agree S' N)
    (j : ℕ) {c : EClause Voc} (hψ : c.ψ.Basic) (hN : c.trigPreds ⊆ N) :
    TrigSem S j c.π c.ψ = TrigSem S' j c.π c.ψ := by
  have hψN : c.ψ.names ⊆ N := by
    rw [names_basic hψ]; intro q hq
    obtain ⟨a, ha, rfl⟩ := hq
    exact hN ⟨a, Or.inr ha, rfl⟩
  have hκN : ∀ κ ∈ c.π, κ.toFormula.names ⊆ N := by
    intro κ hκ
    rw [names_basic (conj_basic κ)]; intro q hq
    obtain ⟨a, ha, rfl⟩ := hq
    refine hN ⟨a, Or.inl ⟨κ, hκ, ?_⟩, rfl⟩
    clear hκ hN hψN
    induction κ with
    | nil => simp [GConj.toFormula, Formula.atoms] at ha
    | cons γ κ ih =>
      simp only [GConj.toFormula, List.foldr_cons, Formula.atoms] at ha
      rcases ha with ha | ha
      · cases γ with
        | pred p ts => simp [GAtom.toFormula, Formula.atoms] at ha; subst ha; simp
        | eq => simp [GAtom.toFormula, Formula.atoms] at ha
      · exact List.mem_cons_of_mem _ (ih ha)
  have hsat : ∀ v, c.ψ.sat S v j ↔ c.ψ.sat S' v j := fun v =>
    Formula.sat_agree _ _ _ _ _ (h.mono hψN)
  have hκ : ∀ κ ∈ c.π, ∀ v, κ.toFormula.sat S v j ↔ κ.toFormula.sat S' v j := fun κ hκ v =>
    Formula.sat_agree _ _ _ _ _ (h.mono (hκN κ hκ))
  unfold TrigSem
  split
  · ext v; simp only [Set.mem_setOf_eq, hsat]
  · ext v; simp only [Set.mem_setOf_eq, hsat]
    exact and_congr_left fun _ => exists_congr fun κ => and_congr_right fun hk =>
      and_congr_right fun _ => hκ κ hk v

theorem icc_inj {n m : ℕ} (h : Interval.icc n n le_rfl = Interval.icc m m le_rfl) : n = m := by
  have : n ∈ Interval.icc m m le_rfl := h ▸ (by simp : n ∈ Interval.icc n n le_rfl)
  simp at this; omega

/-- Componentwise union. -/
def Trip.union (x y : Trip Voc) : Trip Voc := (x.1 ∪ y.1, x.2.1 ∪ y.2.1, x.2.2 ∪ y.2.2)

theorem Trip.le_union (x y : Trip Voc) : x.le (x.union y) :=
  ⟨Set.subset_union_left, Set.subset_union_left, Set.subset_union_left⟩

namespace Setup
variable (U : Setup Voc)

/-- The input of one time-point. -/
structure PtIn where
  H : List (ℕ × DB Voc.toSignature)
  τ : ℕ
  D : Set (REv Voc)
  hH : ∀ m (hm : m < H.length), ∀ ev ∈ H[m].2, ¬ IsLet U.L.lets ev.e
  hmono : ∀ m (hm : m < H.length), H[m].1 ≤ τ
  hD : U.Good D

namespace PtIn
variable {U} (I : U.PtIn)

/-- The events of the time-point in the state `x`. -/
def Xof (x : Trip Voc) : Set (REv Voc) := (I.D \ x.2.2) ∪ x.2.1

/-- The let structure in the state `x`. -/
noncomputable def St (x : Trip Voc) : Str Voc.toSignature := U.SA I.H I.τ (REv.toDB (I.Xof x))

theorem good_X {x : Trip Voc} (hx : U.Good x.2.1) : U.Good (I.Xof x) := by
  rintro y (⟨hy, -⟩ | hy)
  · exact I.hD y hy
  · exact hx y hy

/-- The point context of a state. -/
def toCtx (x : Trip Voc) (hx : U.Good x.2.1) : U.PtCtx :=
  ⟨I.H, I.τ, I.D, x.2.1, x.2.2, I.hH, I.good_X hx, I.hmono⟩

/-- The rows that fire the clause `c` in the state `x`. -/
def A (c : EClause Voc) (x : Trip Voc) : Set (List Voc.𝔻) :=
  {a | ∃ v ∈ TrigSem (I.St x) I.H.length c.π c.ψ, Term.evalList v c.ε.args = some a}

/-- What the clause `c` adds in the state `x`; `len` is `|σ|`. -/
def Δ (len : ℕ) (c : EClause Voc) (x : Trip Voc) : Trip Voc :=
  match c.ε with
  | .cau e _ => (∅, {y | y.1 = e ∧ y.2 ∈ I.A c x}, ∅)
  | .sup e _ => (∅, ∅, {y | y.1 = e ∧ y.2 ∈ I.A c x})
  | .ev J e _ => ({o | ∃ n, J = Interval.icc n n le_rfl ∧ o.1.1 = e ∧ o.1.2 ∈ I.A c x ∧
      o.2 = (.ts, I.τ + n)}, ∅, ∅)
  | .nexts n e _ => ({o | o.1.1 = e ∧ o.1.2 ∈ I.A c x ∧ o.2 = (.tp, len + n)}, ∅, ∅)

theorem trig_sem {c : EClause Voc} {trig : Clause Voc} (ht : toClause c.π c.ψ = some trig)
    {x : Trip Voc} (hx : U.Good x.2.1) :
    trig.sem (Interp U.P ⟨TablesOf U.L.lets I.H, I.τ, I.D, x.2.1, x.2.2⟩) =
      TrigSem (I.St x) I.H.length c.π c.ψ :=
  clause_sem (N := Set.univ) (fun q _ => (I.toCtx x hx).interp _ (fun _ => Or.inl rfl) q)
    (Set.subset_univ _) ht

/-- **One rule application** adds what its clause fires. -/
theorem upd_rule {c : EClause Voc} {it : Item Voc} (h : RuleSpec c it) (σ : Trace Voc.toSignature)
    {x : Trip Voc} (hx : U.Good x.2.1) :
    upd U.P (TablesOf U.L.lets I.H) I.τ I.D σ it x = x.union (I.Δ (Trace.len σ) c x) := by
  obtain ⟨Ω, C, S⟩ := x
  cases h with
  | cau e ts trig hε ht =>
    have := I.trig_sem ht hx
    simp only [upd, Update, this]
    simp only [Δ, hε, Trip.union, Set.union_empty, A, Effect.args]
    congr 2; ext y; obtain ⟨y1, y2⟩ := y; simp [eq_comm, and_comm]
  | sup e ts trig hε ht =>
    have := I.trig_sem ht hx
    simp only [upd, Update, this]
    simp only [Δ, hε, Trip.union, Set.union_empty, A, Effect.args]
    congr 2; ext y; obtain ⟨y1, y2⟩ := y; simp [eq_comm, and_comm]
  | ev n e ts trig hε ht =>
    have := I.trig_sem ht hx
    simp only [upd, Update, this]
    simp only [Δ, hε, Trip.union, Set.union_empty, A, Effect.args]
    congr 1; congr 1; ext o; obtain ⟨⟨o1, o2⟩, o3⟩ := o
    simp only [Set.mem_setOf_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, ⟨rfl, rfl⟩, h3⟩; exact ⟨n, rfl, rfl, ha, h3⟩
    · rintro ⟨n', hn, rfl, h2, h3⟩
      rw [← icc_inj hn] at h3
      exact ⟨o2, h2, ⟨rfl, rfl⟩, h3⟩
  | nexts n e ts trig hε ht =>
    have := I.trig_sem ht hx
    simp only [upd, Update, this]
    simp only [Δ, hε, Trip.union, Set.union_empty, A, Effect.args]
    congr 1; congr 1; ext o; obtain ⟨⟨o1, o2⟩, o3⟩ := o
    simp only [Set.mem_setOf_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, ⟨rfl, rfl⟩, h3⟩; exact ⟨rfl, ha, h3⟩
    · rintro ⟨rfl, h2, h3⟩; exact ⟨o2, h2, ⟨rfl, rfl⟩, h3⟩

end PtIn

end Setup

end Paper
