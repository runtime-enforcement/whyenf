/-
  No event is caused and suppressed: the cause/suppress check of §4.5.
-/
import Paper.Proof.Sat

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem withLets_sat (ℒ : List (LetDef Voc)) (φ : Formula Voc) :
    ∀ (S : Str Voc.toSignature) v i, (withLets ℒ φ).sat S v i ↔ φ.sat (applyLets ℒ S) v i := by
  induction ℒ with
  | nil => intros; rfl
  | cons d ℒ ih => intro S v i; exact ih _ v i

/-- A valuation that fires a compiled trigger satisfies the trigger formula. -/
theorem trigSem_sat {S : Str Voc.toSignature} {j : ℕ} {c : EClause Voc} (hg : c.Guarded)
    {v : Val Voc} (hv : v ∈ TrigSem S j c.π c.ψ) (d : Voc.𝔻) :
    c.trig.sat S (v.ext d) j ∧ Term.evalList (v.ext d) c.ε.args = Term.evalList v c.ε.args := by
  by_cases hπ : c.π = [[]]
  · have hT := trigSem_top S j c.ψ
    rw [← hπ] at hT
    rw [hT] at hv
    obtain ⟨hd, hs⟩ := hv
    have h0 := hg [] (by rw [hπ]; simp)
    simp only [GConj.toFormula, List.foldr_nil, Formula.fv, Set.subset_empty_iff,
      Set.union_empty_iff] at h0
    refine ⟨⟨by rw [hπ]; simp [sat_disj, sat_conj], ?_⟩, ?_⟩
    · exact (Formula.sat_congr _ S _ _ j fun x hx => by rw [h0.1] at hx; exact absurd hx (Set.notMem_empty _)).1 hs
    · exact Term.evalList_congr _ _ _ fun x hx => by rw [h0.2] at hx; exact absurd hx (Set.notMem_empty _)
  · rw [trigSem_ne S j hπ] at hv
    obtain ⟨⟨κ, hκ, hd, hs⟩, hψ⟩ := hv
    have hcov : v.Covers κ.toFormula.fv := fun x hx => by
      have : x ∈ v.dom := hd ▸ hx; exact this
    have hag := Val.ext_agree d hcov
    have hgk := hg κ hκ
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [sat_disj]; exact ⟨κ, hκ, (Formula.sat_congr _ S _ _ j hag).2 hs⟩
    · exact (Formula.sat_congr _ S _ _ j fun x hx => hag x (hgk (Or.inl hx))).2 hψ
    · exact Term.evalList_congr _ _ _ fun x hx => hag x (hgk (Or.inr hx))

/-- A firing of a clause, as needed by the SMT query. -/
def Fired (ℒ : List (LetDef Voc)) (c : EClause Voc) (a : List Voc.𝔻) : Prop :=
  ∃ (σ₁ : Str Voc.toSignature) (i₁ : ℕ) (v₁ : Val Voc), v₁.Covers c.trig.fv ∧
    (withLets ℒ c.trig).sat σ₁ v₁ i₁ ∧ Term.evalList v₁ c.ε.args = some a

namespace Setup
variable (U : Setup Voc)

theorem SCCBefore.rank {e₀ e : Voc.ℰ} (h : SCCBefore U.L.lets U.R e₀ e) : U.rk e₀ < U.rk e := by
  obtain ⟨h1, h2⟩ := h
  have hle : U.rk e₀ ≤ U.rk e := by
    clear h2
    induction h1 with
    | refl => exact le_rfl
    | tail _ he ih => exact le_trans ih (U.topo.2 _ _ he)
  rcases Nat.lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd ((U.topo.1 e₀ e).2 h).2 h2

theorem SCCBefore.noLet {e₀ e : Voc.ℰ} (h : SCCBefore U.L.lets U.R e₀ e) : ¬ IsLet U.L.lets e₀ := by
  obtain ⟨h1, h2⟩ := h
  cases h1.cases_head with
  | inl h' => subst h'; exact absurd Relation.ReflTransGen.refl h2
  | inr h' =>
    obtain ⟨c', ⟨c, a, hc, ⟨q, hq, hd⟩, -⟩, -⟩ := h'
    exact hd.base_end

namespace PtIn
variable {U} (I : U.PtIn) (σ : Trace Voc.toSignature)

theorem fired_of_A {c : EClause Voc} (hc : c ∈ U.R) {x : Trip Voc} {a : List Voc.𝔻}
    (ha : a ∈ I.A c x) : ∃ w : Val Voc, w.Covers c.trig.fv ∧
      (withLets U.L.lets c.trig).sat (strOf I.H I.τ (REv.toDB (I.Xof x))) w I.H.length ∧
      Term.evalList w c.ε.args = some a := by
  obtain ⟨v, hv, hva⟩ := ha
  obtain ⟨h1, h2⟩ := trigSem_sat (U.R_props c hc).2 hv U.Ξ.zero
  exact ⟨v.ext U.Ξ.zero, Val.ext_covers _ _ _, (withLets_sat _ _ _ _ _).2 h1, h2.trans hva⟩

/-- **No event is caused and suppressed** at a time-point, if the events caused
    initially come from deferred clauses. -/
theorem conflict_free (C₀ : Set (REv Voc)) (hC₀ : U.Good C₀)
    (hC₀f : ∀ e ∈ C₀, ∃ c ∈ U.R, c.ε.deferred = true ∧ c.ε.pol = .C ∧ c.ε.name = e.1 ∧
      Fired U.L.lets c e.2)
    (Ω₀ : Set (Obligation Voc)) (TN : Tables Voc) {T' : Tables Voc} {C S : Set (REv Voc)}
    {Ω : Set (Obligation Voc)}
    (h : Saturate U.P ⟨TablesOf U.L.lets I.H, I.τ, I.D, C₀, ∅⟩ TN Ω₀ σ = some (T', C, S, Ω)) :
    ∀ e ∈ S, e ∉ C := by
  obtain ⟨-, -, -, -, hprov⟩ := I.saturate_sem σ C₀ hC₀ Ω₀ TN h
  intro e heS heC
  -- the suppression
  obtain ⟨c₂, hc₂, x₂, -, hx₂g, hag₂, hΔ₂⟩ := hprov (.inr (.inr e)) ⟨heS, by simp⟩
  simp only [InΔ, Δ] at hΔ₂
  cases hε₂ : c₂.ε with
  | cau _ _ | ev _ _ _ | nexts _ _ _ => rw [hε₂] at hΔ₂; exact absurd hΔ₂ (Set.notMem_empty _)
  | sup e₂ ts₂ =>
    rw [hε₂] at hΔ₂
    obtain ⟨he₂, ha₂⟩ := hΔ₂
    obtain ⟨w₂, hw₂c, hw₂s, hw₂a⟩ := I.fired_of_A hc₂ ha₂
    have hpol₂ : c₂.ε.pol = .S := by rw [hε₂]; rfl
    have hname₂ : c₂.ε.name = e.1 := by rw [hε₂, he₂]; rfl
    by_cases h0 : e ∈ C₀
    · -- a deferred cause
      obtain ⟨c₁, hc₁, hdef, hpol₁, hname₁, σ₁, i₁, v₁, hv₁c, hv₁s, hv₁a⟩ := hC₀f e h0
      refine U.conflict c₁ hc₁ c₂ hc₂ hpol₁ hpol₂ (hname₁.trans hname₂.symm) ?_
      rw [hdef]; simp only [↓reduceIte]
      exact ⟨σ₁, _, i₁, _, v₁, w₂, trivial, hv₁c, hw₂c, hv₁s, hw₂s, e.2, hv₁a, hw₂a⟩
    · -- an immediate cause in the same section
      obtain ⟨c₁, hc₁, x₁, -, hx₁g, hag₁, hΔ₁⟩ := hprov (.inr (.inl e)) ⟨heC, h0⟩
      simp only [InΔ, Δ] at hΔ₁
      cases hε₁ : c₁.ε with
      | sup _ _ | ev _ _ _ | nexts _ _ _ => rw [hε₁] at hΔ₁; exact absurd hΔ₁ (Set.notMem_empty _)
      | cau e₁ ts₁ =>
        rw [hε₁] at hΔ₁
        obtain ⟨he₁, ha₁⟩ := hΔ₁
        obtain ⟨w₁, hw₁c, hw₁s, hw₁a⟩ := I.fired_of_A hc₁ ha₁
        have hname₁ : c₁.ε.name = e.1 := by rw [hε₁, he₁]; rfl
        refine U.conflict c₁ hc₁ c₂ hc₂ (by rw [hε₁]; rfl) hpol₂ (hname₁.trans hname₂.symm) ?_
        have hnd : c₁.ε.deferred = false := by rw [hε₁]; rfl
        rw [hnd]; simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨strOf I.H I.τ (REv.toDB (I.Xof x₁)), strOf I.H I.τ (REv.toDB (I.Xof x₂)), _, _, w₁,
          w₂, ⟨⟨rfl, fun j ev hev => ?_⟩, rfl⟩, hw₁c, hw₂c, hw₁s, hw₂s, e.2, hw₁a, hw₂a⟩
        have hr : U.rk ev.e < U.rk e.1 := by rw [← hname₁]; exact SCCBefore.rank U hev
        have hr₁ : U.rk ev.e < U.rk c₁.ε.name := by rw [hname₁]; exact hr
        have hr₂ : U.rk ev.e < U.rk c₂.ε.name := by rw [hname₂]; exact hr
        have a1 := hag₁ (ev.e, ev.args) hr₁
        have a2 := hag₂ (ev.e, ev.args) hr₂
        simp only [strOf]
        split_ifs
        all_goals try exact Iff.rfl
        simp only [REv.toDB, Set.mem_setOf_eq, Xof, Set.mem_union, Set.mem_diff]
        rw [a1.1, a1.2, a2.1, a2.2]

end PtIn

end Setup

end Paper
