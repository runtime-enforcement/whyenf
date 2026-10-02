/-
  Histories, and what compiled triggers and lets compute on them.
-/
import Paper.Proof.Basic2

namespace Paper

open Classical

variable {Voc : Vocabulary}

mutual
theorem Term.eval_covers (v : Val Voc) :
    ∀ t : Term Voc, (t.eval v).isSome → v.Covers t.vars
  | .var y, h => by intro x hx; simp [Term.vars] at hx; subst hx; exact h
  | .const _, _ => by intro x hx; simp [Term.vars] at hx
  | .app f ts, h => by
    simp only [Term.eval, Option.bind_eq_bind] at h
    refine Term.evalList_covers v ts ?_
    cases h' : Term.evalList v ts <;> simp_all
theorem Term.evalList_covers (v : Val Voc) :
    ∀ ts : List (Term Voc), (Term.evalList v ts).isSome → v.Covers (Term.varsList ts)
  | [], _ => by intro x hx; simp [Term.varsList] at hx
  | t :: ts, h => by
    simp only [Term.evalList, Option.bind_eq_bind] at h
    have h1 : (Term.eval v t).isSome := by cases h1 : Term.eval v t <;> simp_all
    have h2 : (Term.evalList v ts).isSome := by
      cases h1 : Term.eval v t <;> cases h2 : Term.evalList v ts <;> simp_all
    rintro x (hx | hx)
    · exact Term.eval_covers v t h1 x hx
    · exact Term.evalList_covers v ts h2 x hx
end

theorem conj_sat_covers {S : Str Voc.toSignature} {v : Val Voc} {i : ℕ} :
    ∀ {κ : GConj Voc}, κ.toFormula.sat S v i → v.Covers κ.toFormula.fv := by
  intro κ h
  rw [fv_gconj]
  rintro x ⟨γ, hγ, hx⟩
  have hs := (sat_conj S v i κ).1 h γ hγ
  cases γ with
  | pred p ts =>
    simp only [GAtom.toFormula, Formula.fv, Formula.sat] at hx hs
    obtain ⟨ds, hds, -⟩ := hs
    exact Term.evalList_covers v ts (by simp [hds]) x hx
  | eq y c =>
    simp only [GAtom.toFormula, Formula.fv, Formula.sat, Set.mem_singleton_iff] at hx hs
    subst hx; simp [hs]

theorem trigSem_top (S : Str Voc.toSignature) (j : ℕ) (ψ : Formula Voc) :
    TrigSem S j [[]] ψ = {v | v.dom = ψ.fv ∧ ψ.sat S v j} := rfl

theorem trigSem_ne (S : Str Voc.toSignature) (j : ℕ) {π : GDisj Voc} (hπ : π ≠ [[]])
    (ψ : Formula Voc) :
    TrigSem S j π ψ =
      {v | (∃ κ ∈ π, v.dom = κ.toFormula.fv ∧ κ.toFormula.sat S v j) ∧ ψ.sat S v j} := by
  unfold TrigSem; split
  · exact absurd rfl hπ
  · rfl

/-- **Compiled guards.** If `Guards^m_X(Φ) = (π, ψ)` with `fv(Φ) ⊆ X`, the trigger
    `(π, ψ)` fires for exactly the valuations on `X` that satisfy `Φ`. -/
theorem trigSem_guards {m : Set Voc.ℰ} {X : Set Voc.𝕍} {Φ : Formula Voc} {π : GDisj Voc}
    {ψ : Formula Voc} (h : Guards m X Φ = some (π, ψ)) (hX : Φ.fv ⊆ X)
    (S : Str Voc.toSignature) (j : ℕ) :
    TrigSem S j π ψ = {v | v.dom = X ∧ Φ.sat S v j} := by
  have hg := Guards_spec h
  obtain ⟨hb, he⟩ := lemma_4_2 h
  have hfvψ : ψ.fv ⊆ X := hg.fv_filter.trans hX
  -- every disjunct has exactly the variables `X`
  have hκX : ∀ κ ∈ π, κ.toFormula.fv = X := by
    intro κ hκ
    refine le_antisymm ((hg.fv_sub κ hκ).trans hX) fun x hx => Binds.mem_fv (hb κ hκ x hx)
  by_cases hπ : π = [[]]
  · subst hπ
    have hX0 : X = ∅ := by
      rw [← hκX [] (by simp)]; simp [GConj.toFormula, Formula.fv]
    have hψ0 : ψ.fv = ∅ := Set.subset_eq_empty hfvψ hX0
    rw [trigSem_top]
    ext v
    simp only [Set.mem_setOf_eq, hψ0, hX0]
    refine and_congr_right fun _ => ?_
    have := he S v j
    simp only [Formula.sat, sat_disj, sat_conj] at this
    rw [← this]; simp
  · rw [trigSem_ne S j hπ]
    ext v
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨κ, hκ, hd, hs⟩, hψ⟩
      refine ⟨by rw [hd, hκX κ hκ], (he S v j).1 ⟨?_, hψ⟩⟩
      rw [sat_disj]; exact ⟨κ, hκ, hs⟩
    · rintro ⟨hd, hΦ⟩
      obtain ⟨hπ', hψ⟩ := (he S v j).2 hΦ
      rw [sat_disj] at hπ'
      obtain ⟨κ, hκ, hs⟩ := hπ'
      exact ⟨⟨κ, hκ, by rw [hd, hκX κ hκ], hs⟩, hψ⟩

/-! ## Histories -/

/-- The structure of a history `H` (time-points `0 … |H|-1`) with current
    time-point `(τ, D)` at `|H|`, and no events afterwards. -/
noncomputable def strOf (H : List (ℕ × DB Voc.toSignature)) (τ : ℕ) (D : DB Voc.toSignature) :
    Str Voc.toSignature where
  τ := fun k => if h : k < H.length then H[k].1 else τ
  D := fun k => if h : k < H.length then H[k].2 else if k = H.length then D else ∅

section
variable (H : List (ℕ × DB Voc.toSignature)) (τ : ℕ) (D : DB Voc.toSignature)

theorem strOf_τ_lt {k : ℕ} (hk : k < H.length) : (strOf H τ D).τ k = H[k].1 := by
  simp [strOf, hk]
theorem strOf_D_lt {k : ℕ} (hk : k < H.length) : (strOf H τ D).D k = H[k].2 := by
  simp [strOf, hk]
theorem strOf_τ_len : (strOf H τ D).τ H.length = τ := by simp [strOf]
theorem strOf_D_len : (strOf H τ D).D H.length = D := by simp [strOf]

theorem strOf_past (τ' : ℕ) (D' : DB Voc.toSignature) {m : ℕ} (hm : m < H.length) :
    PastAgree (strOf H τ D) (strOf H τ' D') m := by
  intro k hk
  rw [strOf_τ_lt H τ D (by omega), strOf_τ_lt H τ' D' (by omega), strOf_D_lt H τ D (by omega),
    strOf_D_lt H τ' D' (by omega)]
  exact ⟨rfl, rfl⟩

theorem strOf_snoc_past (τ' : ℕ) (D' : DB Voc.toSignature) :
    PastAgree (strOf H τ D) (strOf (H ++ [(τ, D)]) τ' D') H.length := by
  intro k hk
  rcases Nat.lt_or_eq_of_le hk with hk | rfl
  · rw [strOf_τ_lt H τ D hk, strOf_τ_lt _ τ' D' (by simp; omega), strOf_D_lt H τ D hk,
      strOf_D_lt _ τ' D' (by simp; omega)]
    simp [List.getElem_append_left hk]
  · rw [strOf_τ_len, strOf_D_len, strOf_τ_lt _ τ' D' (by simp), strOf_D_lt _ τ' D' (by simp)]
    simp

end

/-- The tuples `r` such that `φ` holds at `m` for `x̄ ↦ r`. -/
def RowsAt (S : Str Voc.toSignature) (m : ℕ) (φ : Formula Voc) (xs : List Voc.𝕍) :
    Set (List Voc.𝔻) :=
  {r | ∃ v : Val Voc, v.Covers {x | x ∈ xs} ∧ xs.map v = r.map some ∧ φ.sat S v m}

theorem RowsAt.congr {S S' : Str Voc.toSignature} {m m' : ℕ} {φ φ' : Formula Voc}
    {xs : List Voc.𝕍} (h : ∀ v, φ.sat S v m ↔ φ'.sat S' v m') :
    RowsAt S m φ xs = RowsAt S' m' φ' xs := by
  ext r; simp only [RowsAt, Set.mem_setOf_eq, h]

/-- The content of the table of the let `d` after the history `H`. -/
def TabFor (ℒ : List (LetDef Voc)) (H : List (ℕ × DB Voc.toSignature)) (d : LetDef Voc) :
    Set (ℕ × List Voc.𝔻) :=
  match d.φ with
  | .since _ φl φr =>
    {tr | ∃ m < H.length, tr.1 = (strOf H 0 ∅).τ m ∧
      tr.2 ∈ RowsAt (applyLets ℒ (strOf H 0 ∅)) m φr d.xs ∧
      ∀ m', m < m' → m' < H.length → tr.2 ∈ RowsAt (applyLets ℒ (strOf H 0 ∅)) m' φl d.xs}
  | .prev _ φ =>
    {tr | ∃ m, m + 1 = H.length ∧ tr.1 = (strOf H 0 ∅).τ m ∧
      tr.2 ∈ RowsAt (applyLets ℒ (strOf H 0 ∅)) m φ d.xs}
  | _ => ∅

/-- The tables after the history `H`. -/
def TablesOf (ℒ : List (LetDef Voc)) (H : List (ℕ × DB Voc.toSignature)) : Tables Voc :=
  fun q => {tr | ∃ d ∈ ℒ, d.e = q ∧ tr ∈ TabFor ℒ H d}

theorem TablesOf_nil (ℒ : List (LetDef Voc)) : TablesOf ℒ [] = fun _ => ∅ := by
  funext q; ext tr
  simp only [TablesOf, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro d _ _
  unfold TabFor
  split <;> simp

end Paper
