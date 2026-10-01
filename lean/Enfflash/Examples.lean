/-
  Enfflash formalization — examples.

  1. A counterexample showing that suppressing the *right* operand of
     `φl S_[a,b] φr` with `a > 0` does not suppress the since formula (hence
     `LBody.supTarget` suppresses the left operand).
  2. The policies `φ_law` and `φ_del` of Example 2.3 as `Policy`s, and
     Example A.4: the let-normal form of `φ_del`, its typing
     `Γ ⊢ χ : ℂ ▷ Δ`, hence `φ_del ∈ EF-MFOTL` (Definition A.2) and, by
     Theorem A.3, a successful compilation with clause set `Δ`.
  3. The aggregation `φ_agg` of Example 2.3 with the operator `CNT`, in a
     policy whose let-normal form binds it to a let.
-/
import Enfflash.Tables
import Enfflash.Rewrite
import Enfflash.EndToEnd
import Mathlib.Data.ENat.Lattice

namespace Enfflash.Examples

inductive E | A | B

/-! ### The since counterexample -/

/-- A trace with `B(1)` at time-point 0 (timestamp 0) and nothing at
    time-point 1 (timestamp 1). -/
def σ : Tr E Empty ℕ where
  db i := if i = 0 then {(.base .B, [1])} else ∅
  ts i := i
  lv _ p := p.elim

open Fm in
/-- `⊤ S_[1,∞) B(x)` holds at time-point 1 for `x = 1`, although its right
    operand `B(x)` does not hold there: suppressing `φr` now does not falsify
    the since formula when `a > 0`. -/
example : ¬ σ.sat 1 (vcons 1 (fun _ => 0)) (pred (.ev (.base .B)) [.var 0]) ∧
    (LBody.since 1 none tt (pred (.ev (.base .B)) [.var 0])).sem σ 1 (vcons 1 (fun _ => 0)) := by
  refine ⟨by simp [Tr.sat, Tr.prIn, σ], ⟨0, by omega, ⟨by simp [σ], by simp⟩, ?_, ?_⟩⟩
  · simp [Tr.sat, Tr.prIn, σ, Term.eval]; try rfl
  · intros; trivial

/-! ### The running examples (Example 2.3 and Example A.4) -/

/-- The event names of Example 2.1. -/
inductive Ev0 | use | consent | revoke | delete | deleteReq

open MF in
/-- `φ_law = □ ∀c,d,u. use(c,d,u) → (¬revoke(u,c) S consent(u,c))`, as
    `¬∃c,d,u. use(c,d,u) ∧ ¬(¬revoke(u,c) S consent(u,c))` (de Bruijn:
    `u = 0`, `d = 1`, `c = 2`). -/
def phiLaw : MF Ev0 ℕ :=
  neg (ex (ex (ex (conj (pred .use [.var 2, .var 1, .var 0])
    (neg (since 0 none (neg (pred .revoke [.var 0, .var 2])) (pred .consent [.var 0, .var 2])))))))

open MF in
/-- `φ_del = □ ∀d,u. deletion_request(d,u) → ◇_[0,30] delete(d,u)`, as
    `¬∃d,u. deletion_request(d,u) ∧ ¬◇_[0,30] delete(d,u)` (`u = 0`, `d = 1`). -/
def phiDel : MF Ev0 ℕ :=
  neg (ex (ex (conj (pred .deleteReq [.var 1, .var 0])
    (neg (ev 0 30 (pred .delete [.var 1, .var 0]))))))

/-- `φ_law` is a policy (well-formed, with future-free past operators). -/
def lawPolicy : Policy Ev0 ℕ :=
  ⟨phiLaw, by simp [phiLaw, MF.WF, Term.WF], by simp [phiLaw, MF.PastPure, MF.ffree]⟩

/-- `φ_del` is a policy. -/
def delPolicy : Policy Ev0 ℕ :=
  ⟨phiDel, by simp [phiDel, MF.WF, Term.WF], by simp [phiDel, MF.PastPure]⟩

open Fm in
/-- Example A.4: the let-normal form of `φ_del` is `□ ¬∃d,u. φ₀` with no lets,
    `φ₀ = deletion_request(d,u) ∧ ¬◇_[0,30] delete(d,u)`. -/
theorem lnf_phiDel :
    lnf phiDel = (neg (ex (ex (conj (pred (.ev (.base .deleteReq)) [.var 1, .var 0])
      (neg (ev 0 30 (pred (.ev (.base .delete)) [.var 1, .var 0])))))), []) := rfl

/-- The signature of Example A.4: `delete` is causable, nothing is
    suppressable. -/
def S₀ : Sig Ev0 ℕ ℕ where
  cau e := e = .delete
  sup _ := False
  enum _ := True
  ar _ := 0
  okC _ := False
  okS _ := False
  d₀ := 0

/-- The clause `(deletion_request(d,u), ⊤) ⇒ ◇_[30,30] delete(d,u)` of
    Example A.4, i.e. the EF rule
    `rule +delete(d,u) [delay 30] := trigger {deletion_request(d,u)}`. -/
def delRule : Clause Ev0 ℕ ℕ :=
  ⟨2, ⟨[[.pred (.ev (.base .deleteReq)) [.var 1, .var 0]]], .conj .tt .tt⟩,
    .later 30 (.base .delete) [.var 1, .var 0]⟩

/-- The clause after extracting a guard for `u`. -/
def delRule₁ : Clause Ev0 ℕ ℕ :=
  ⟨1, ⟨[[.pred (.ev (.base .deleteReq)) [.var 1, .var 0]]], .conj .tt .tt⟩,
    .later 30 (.base .delete) [.var 1, .var 0]⟩

/-- No let capabilities (there are no lets). -/
def κ₀ : Caps := ⟨fun _ => False, fun _ => False, fun _ => False⟩

/-- **Example A.4.**  `φ_del` is in EF-MFOTL with clause set `{delRule}`. -/
theorem phiDel_efmfotl : EFMFOTL S₀ phiDel [delRule] := by
  refine ⟨κ₀, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro p d h; simp [lnf_phiDel] at h
  · intro p d a b φl φr h; simp [lnf_phiDel] at h
  · intro p d h; simp [lnf_phiDel] at h
  · intro p d k ω ts ys φ h; simp [lnf_phiDel] at h
  · intro p _; exact ⟨id, id, id⟩
  · intro p h; exact h.elim
  · intro p h; exact h.elim
  rw [show (lnf phiDel).1 = _ from congrArg Prod.fst lnf_phiDel]
  -- ◇_[0,30] delete(d,u) : ℂ ▷ {⊤ ⇒ ◇_[30,30] delete(d,u)}   (Ev^ℂ, Fut_◇^ℂ)
  have hfut := Typ.futEv (S := sigOf S₀ (enumCaps κ₀) κ₀.C κ₀.S) (a := 0) (b := 30)
    (Typ.evC (e := Ev0.delete) (ts := [.var 1, .var 0]) rfl) (by omega) (by omega)
    (by simp) (by simp [Clause.simple, Trigger.top])
  -- φ₀ : 𝕊 ▷ {(⊤, deletion_request(d,u)) ⇒ ◇_[30,30] delete(d,u)}   (Neg^𝕊, And^𝕊_R)
  have hφ₀ := Typ.andSR (φ := .pred (.ev (.base .deleteReq)) [.var 1, .var 0])
    (Typ.neg hfut) trivial
  -- two applications of Ex^𝕊 (guards from `Pred`, then `Grd`), and Neg^ℂ
  refine Typ.neg (Typ.exS (Typ.exS (Δ' := [delRule₁]) hφ₀ (.cons ⟨rfl, rfl, ?_⟩ .nil))
    (.cons ⟨rfl, rfl, ?_⟩ .nil))
  · exact GX.andR (GX.pred trivial (by simp [Clause.addFilter, Clause.mapCau, Term.subst, liftS]))
  · exact GX.grd (by simp [Guards.bindsAll, GAtom.binds, delRule₁])

/-- By Theorem A.3, the compilation of `φ_del` succeeds with clause set
    `{delRule}`. -/
theorem phiDel_compiles : Compiles S₀ phiDel [delRule] :=
  (efmfotl_iff_compiles S₀ phiDel [delRule]).1 phiDel_efmfotl

/-! ### Aggregation (Example 2.3, `φ_agg`) -/

/-- `CNT`: the number of rows (with multiplicity) of a multiset. -/
noncomputable def CNT : AggOp ℕ where
  op M r := ∃ n : ℕ, r = [n] ∧ (n : ℕ∞) = ⨆ s : Finset (List ℕ), ∑ x ∈ s, M x
  fin M _ _ := by
    refine Set.Subsingleton.finite ?_
    rintro r ⟨n, rfl, hn⟩ r' ⟨n', rfl, hn'⟩
    rw [← hn'] at hn
    simp only [Nat.cast_inj] at hn
    rw [hn]

open MF in
/-- `n ← CNT(d; u) ⧫_[0,10] use(c,d,u)`: the number of data items of user `u`
    used in the last 10 time units (aggregated variables `d = 0`, `c = 1`;
    group `u` = outer variable `0`, result `n` = outer variable `1`). -/
noncomputable def phiAgg : MF Ev0 ℕ :=
  agg 2 CNT [.var 0] [1] (since 0 (some 10) tt (pred .use [.var 1, .var 0, .var 2]))

open MF in
/-- A policy with an aggregation: no user has 1000 uses in the last 10 time
    units, `□ ¬∃u,n. φ_agg(u,n) ∧ n = 1000`. -/
noncomputable def aggPolicy : Policy Ev0 ℕ :=
  ⟨neg (ex (ex (conj phiAgg (eq (.var 0) (.const 1000))))),
    by simp [phiAgg, MF.WF, Term.WF], by simp [phiAgg, MF.PastPure, MF.ffree]⟩

/-- Its let-normal form binds the since subformula (`0`, over `c, d, u`), the
    aggregation (`1`, over `u, n`), and the two (future-free) existentials to
    lets. -/
theorem aggPolicy_lnf :
    (lnf aggPolicy.φ).2.map (fun d => d.arity) = [3, 2, 1, 0] ∧
      (∃ k ω ts ys φ, ((lnf aggPolicy.φ).2[1]?).map LetDef.body = some (.agg k ω ts ys φ)) := by
  refine ⟨rfl, _, _, _, _, _, rfl⟩

end Enfflash.Examples
