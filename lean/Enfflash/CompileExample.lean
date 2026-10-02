/-
  EnfFlash formalization — the compiler on Example A.4: `compile` returns, for
  `φ_del`, a program whose clause set is exactly the paper's
  `(deletion_request(d,u), ⊤) ⇒ ◇_[30,30] delete(d,u)`, i.e. the EF rule
  `rule +delete(d,u) [delay 30] := trigger {deletion_request(d,u)}`.
-/
import Enfflash.Compile
import Enfflash.Examples

namespace Enfflash.Examples

/-- The rewriting of the enforced formula of `φ_del` yields the paper's clause set. -/
theorem rw_phiDel (gd : ℕ → Option (Guards Ev0 ℕ ℕ)) (R : Real Ev0 ℕ ℕ) :
    rw (R.scope (sigOf S₀ (enumOf gd) (fun _ => False) (fun _ => False)) (fun _ => True)) true
      (lnf phiDel).1 = some [[delRule]] := by
  set S := R.scope (sigOf S₀ (enumOf gd) (fun _ => False) (fun _ => False)) (fun _ => True)
  have e₁ : exGuard S ⟨0, ⟨Guards.top, Fm.tt.conj (Fm.pred (Pr.ev (Ev.base Ev0.deleteReq)) [Term.var 1, Term.var 0])⟩,
      Effect.later 30 (Ev.base Ev0.delete) [Term.var 1, Term.var 0]⟩ = some delRule₁ := by
    simp [exGuard, gx, Guards.top, Guards.bindsAll, GAtom.binds, S, Real.scope, sigOf, enumOf,
      Guards.addAtom, delRule₁]
  have e₂ : exGuard S delRule₁ = some delRule := by
    simp [exGuard, gx, Guards.bindsAll, GAtom.binds, delRule₁, delRule]
  have hcau : S.cau Ev0.delete := by simp [S, Real.scope, sigOf, S₀]
  rw [show (lnf phiDel).1 = _ from congrArg Prod.fst lnf_phiDel]
  simp [rw, Fm.present, Clause.simple, Trigger.top, Clause.mapCau, Clause.addFilter, hcau,
    Trigger.andFilter, Fm.subst, Term.subst, liftS, e₁, e₂]

/-- Only variables and constants labelled stable (no `sfun`s). -/
theorem stab_id : ∃ Stab : Set ℕ → Set ℕ, StabOp Stab ∧ ∀ t : Term ℕ, t.stable → t.stableIn Stab :=
  ⟨id, ⟨fun _ => le_rfl, fun _ _ h => h, fun _ => le_rfl, fun _ h => h⟩,
    fun t ht => by cases t <;> simp_all [Term.stable, Term.stableIn]⟩

/-- `Generate` on Example A.4 yields the paper's clause set. -/
theorem compilations_phiDel : ∃ x ∈ compilations S₀ delPolicy.φ, x.1 = [delRule] := by
  have hT : TemporalOK (lnf delPolicy.φ).2 := by
    intro p d hd; simp [delPolicy, lnf_phiDel] at hd
  have hrw : rw ((realOf (lnf delPolicy.φ).2 S₀).scope (sig0 (lnf delPolicy.φ).2 S₀) (fun _ => True))
      true (lnf delPolicy.φ).1 = some [[delRule]] :=
    rw_phiDel (gdOf (lnf delPolicy.φ).2) (realOf (lnf delPolicy.φ).2 S₀)
  unfold compilations
  rw [dif_pos hT]
  split
  · rename_i h; rw [hrw] at h; cases h
  · rename_i CS h
    rw [hrw] at h; cases h
    simp

/-- **The compiler on Example A.4.** -/
theorem compile_phiDel :
    ∃ P ∈ compile delPolicy S₀ (fun _ => 0) Term.stable stab_id, P.C = [delRule] := by
  obtain ⟨x, hx, h₁⟩ := compilations_phiDel
  obtain ⟨P, hP, h₂⟩ := mem_compile (v₀ := fun _ => 0) (stab := Term.stable) (hstab := stab_id) hx
  exact ⟨P, hP, h₂.trans h₁⟩

/-- **The clauses of the table `Since1` of Figure 2** (`φ_law`): guard
    extraction and simplification give `add {consent(u,c)}` and
    `remove {revoke(u,c)}`, both without filter, as in the emitted EF. -/
theorem since1_clauses (m : Pr Ev0 ℕ → Prop) (hc : m (.ev (.base .consent)))
    (hr : m (.ev (.base .revoke))) :
    (gxj m [0, 1] true (Fm.pred (.ev (.base .consent)) [.var 0, .var 1] : Fm Ev0 ℕ ℕ)).map
        (fun r => (r.1, r.2.simp)) =
      some ([[.pred (.ev (.base .consent)) [.var 0, .var 1]]], .tt) ∧
    (gxj m [0, 1] false (Fm.neg (Fm.pred (.ev (.base .revoke)) [.var 0, .var 1]) : Fm Ev0 ℕ ℕ)).map
        (fun r => (r.1, (Fm.neg r.2).simp)) =
      some ([[.pred (.ev (.base .revoke)) [.var 0, .var 1]]], .tt) := by
  constructor <;> simp [gxj, hc, hr, Fm.simp, Fm.mkNeg]

end Enfflash.Examples
