/-
  Appendix A: a type system for the enforceable fragment (main.tex l.2092–2268,
  extended version): contexts, Figure 6 (guardedness), Figure 7 (causation
  and suppression), the conditions on lets, EF-MFOTL, and the statements of
  Lemma A.1 and Theorem A.2.  The proofs are in `Paper/Proof/TypeSystem.lean`.
-/
import Paper.Dependency

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-! ## Contexts -/

/-- The capabilities `𝔾` (guard), `ℂ` (causable), `𝕊` (suppressable). -/
inductive Cap | G | C | S
  deriving DecidableEq

/-- A context `Γ` assigns to each let-bound event a set of capabilities
    `Γ(p) ⊆ {𝔾, ℂ, 𝕊}` (l.2105–2110). -/
abbrev ACtx (Voc : Vocabulary) := Voc.ℰ → Set Cap

/-- `m_Γ`: base events are always enumerable, and so are the lets with `𝔾`. -/
def ACtx.m (Ξ : RwSetting Voc) (Γ : ACtx Voc) : Set Voc.ℰ := Ξ.base ∪ {p | Cap.G ∈ Γ p}

/-! ## Figure 6: guardedness -/

/-- `m ⊢ φ : GRD(x)^p` (Figure 6), with `m = m_Γ`. -/
inductive Grd (m : Set Voc.ℰ) (x : Voc.𝕍) : Pol → Formula Voc → Prop
  /-- `Pred`: `p ∈ m_Γ`, `x ∈ t̄` -/
  | pred (p : Voc.ℰ) (ts : List (Term Voc)) : p ∈ m → Term.var x ∈ ts → Grd m x .pos (.pred p ts)
  /-- `Eq` -/
  | eq (c : Voc.𝔻) : Grd m x .pos (.eq x c)
  /-- `Vac` -/
  | vac : Grd m x .neg .top
  /-- `Neg` -/
  | neg {p : Pol} {φ : Formula Voc} : Grd m x p.flip φ → Grd m x p (.neg φ)
  /-- `And⁺_L` -/
  | andL {φ ψ : Formula Voc} : Grd m x .pos φ → Grd m x .pos (.and φ ψ)
  /-- `And⁺_R` -/
  | andR {φ ψ : Formula Voc} : Grd m x .pos ψ → Grd m x .pos (.and φ ψ)
  /-- `And⁻` -/
  | andNeg {φ ψ : Formula Voc} : Grd m x .neg φ → Grd m x .neg ψ → Grd m x .neg (.and φ ψ)

/-- `Γ ⊢ φ : GRD(x)^p` -/
def ACtx.Grd (Ξ : RwSetting Voc) (Γ : ACtx Voc) (x : Voc.𝕍) (p : Pol) (φ : Formula Voc) : Prop :=
  Paper.Grd (Γ.m Ξ) x p φ

/-- `Γ ⊢ φ : 𝔾^p_X` iff `Γ ⊢ φ : GRD(x)^p` for all `x ∈ X`. -/
def ACtx.GSet (Ξ : RwSetting Voc) (Γ : ACtx Voc) (p : Pol) (X : Set Voc.𝕍) (φ : Formula Voc) : Prop :=
  ∀ x ∈ X, Γ.Grd Ξ x p φ

/-- A trigger `(π, ψ)` guards `x` if every `κ ∈ π` contains an atom with
    argument `x`, or `Γ ⊢ ψ : GRD(x)⁺` (l.2118–2119). -/
def ACtx.TrigGuards (Ξ : RwSetting Voc) (Γ : ACtx Voc) (π : GDisj Voc) (ψ : Formula Voc)
    (x : Voc.𝕍) : Prop :=
  (∀ κ ∈ π, κ.Binds x) ∨ Γ.Grd Ξ x .pos ψ

/-! ## Figure 7: causation and suppression -/

/-- `Δ^ψ`: `ψ` conjoined to the filter of every trigger. -/
def ClauseSet.conj (Δ : Set (EClause Voc)) (ψ' : Formula Voc) : Set (EClause Voc) :=
  (fun c => (⟨c.π, .and c.ψ ψ', c.ε⟩ : EClause Voc)) '' Δ

/-- `Δ[0/x]` (where defined; NOTES.md, N2). -/
def ClauseSet.subst (Ξ : RwSetting Voc) (x : Voc.𝕍) (Δ : Set (EClause Voc)) : Set (EClause Voc) :=
  (fun c => (⟨(c.π.subst Ξ.zero x).getD c.π, (c.ψ.subst Ξ.zero x).getD c.ψ, c.ε.subst Ξ.zero x⟩ :
    EClause Voc)) '' Δ

/-- `Δ↓ₓ = {(π', ψ') ⇒ ε ∣ (π, ψ) ⇒ ε ∈ Δ, m_Γ ⊢ (π, ψ) ⇝⁺_x (π', ψ')}`. -/
def ClauseSet.down (m : Set Voc.ℰ) (x : Voc.𝕍) (Δ : Set (EClause Voc)) : Set (EClause Voc) :=
  {c' | ∃ c ∈ Δ, TGX m .pos x c.π c.ψ c'.π c'.ψ ∧ c'.ε = c.ε}

/-- `◇_[b,b]Δ`, `○Δ`, `○ⁿΔ` for an unconditional `Δ`. -/
def ClauseSet.defer (f : Voc.ℰ → List (Term Voc) → Effect Voc) (Δ : Set (EClause Voc)) :
    Set (EClause Voc) :=
  (fun c => (⟨GDisj.top, .top, deferEffect f c.ε⟩ : EClause Voc)) '' Δ

/-- The other conjuncts `⋀_{i ≠ j} φᵢ`. -/
def othersConj (φs : List (Formula Voc)) (j : Fin φs.length) : Formula Voc :=
  bigAnd ((List.finRange φs.length).filter (· ≠ j) |>.map fun i => φs[i])

/-- `Γ ⊢ φ : α ▷ Δ` (Figure 7). -/
inductive Typ (Ξ : RwSetting Voc) (Γ : ACtx Voc) : Mode → Formula Voc → Set (EClause Voc) → Prop
  /-- `⊤^ℂ` -/
  | top : Typ Ξ Γ .C .top ∅
  /-- `Ev^ℂ` -/
  | evC (e : Voc.ℰ) (ts : List (Term Voc)) : e ∈ Ξ.Cau →
      Typ Ξ Γ .C (.pred e ts) {⟨GDisj.top, .top, .cau e ts⟩}
  /-- `Ev^𝕊` -/
  | evS (e : Voc.ℰ) (ts : List (Term Voc)) : e ∈ Ξ.Sup →
      Typ Ξ Γ .S (.pred e ts) {⟨[[.pred e ts]], .top, .sup e ts⟩}
  /-- `Let^ℂ` -/
  | letC (e : Voc.ℰ) (ts : List (Term Voc)) : Cap.C ∈ Γ e →
      Typ Ξ Γ .C (.pred e ts) {⟨GDisj.top, .top, .cau (Ξ.cauN e) ts⟩}
  /-- `Let^𝕊` -/
  | letS (e : Voc.ℰ) (ts : List (Term Voc)) : Cap.S ∈ Γ e →
      Typ Ξ Γ .S (.pred e ts) {⟨[[.pred e ts]], .top, .cau (Ξ.supN e) ts⟩}
  /-- `Neg^ℂ` -/
  | negC {φ Δ} : Typ Ξ Γ .S φ Δ → Typ Ξ Γ .C (.neg φ) Δ
  /-- `Neg^𝕊` -/
  | negS {φ Δ} : Typ Ξ Γ .C φ Δ → Typ Ξ Γ .S (.neg φ) Δ
  /-- `And^ℂ` -/
  | andC {φ ψ Δ₁ Δ₂} : Typ Ξ Γ .C φ Δ₁ → Typ Ξ Γ .C ψ Δ₂ → Typ Ξ Γ .C (.and φ ψ) (Δ₁ ∪ Δ₂)
  /-- `And^𝕊` -/
  | andS (φs : List (Formula Voc)) (j : Fin φs.length) {Δ} : 2 ≤ φs.length →
      Typ Ξ Γ .S φs[j] Δ → (∀ i : Fin φs.length, i ≠ j → φs[i].Present) →
      Typ Ξ Γ .S (bigAnd φs) (ClauseSet.conj Δ (othersConj φs j))
  /-- `Ex^ℂ` -/
  | exC (x : Voc.𝕍) {φ Δ} : Typ Ξ Γ .C φ Δ →
      (∀ c ∈ Δ, (c.π.subst Ξ.zero x).isSome ∧ (c.ψ.subst Ξ.zero x).isSome) →
      Typ Ξ Γ .C (.ex x φ) (ClauseSet.subst Ξ x Δ)
  /-- `Ex^𝕊` -/
  | exS (x : Voc.𝕍) {φ Δ} : Typ Ξ Γ .S φ Δ → (∀ c ∈ Δ, Γ.TrigGuards Ξ c.π c.ψ x) →
      Typ Ξ Γ .S (.ex x φ) (ClauseSet.down (Γ.m Ξ) x Δ)
  /-- `Fut_◇^ℂ` -/
  | futEv (a b : ℕ) (h : (a : ℕ∞) ≤ b) {φ Δ} : Typ Ξ Γ .C φ Δ → Δ ≠ ∅ → Uncond Δ → 1 ≤ b →
      Typ Ξ Γ .C (.eventually (Interval.icc a b h) φ)
        (ClauseSet.defer (.ev (Interval.icc b b le_rfl)) Δ)
  /-- `Fut_○^ℂ` -/
  | futNext (b : ℕ∞) {φ Δ} : Typ Ξ Γ .C φ Δ → Δ ≠ ∅ → Uncond Δ → 1 ≤ b →
      Typ Ξ Γ .C (.next (Interval.icc 0 b (by simp)) φ) (ClauseSet.defer (.nexts 1) Δ)
  /-- `Fut_{○ⁿ}^ℂ` -/
  | futNextN (n : ℕ) {φ Δ} : Typ Ξ Γ .C φ Δ → Uncond Δ → 1 ≤ n →
      Typ Ξ Γ .C (nextN n φ) (ClauseSet.defer (.nexts n) Δ)

/-! ## Let bindings -/

/-- `ȳ` of a let body `∃ȳ. ψ`. -/
def stripVars : Formula Voc → List Voc.𝕍
  | .ex x φ => x :: stripVars φ
  | _ => []

/-- `φ̂ᵢ`, the formula producing the tuples of the body `χ = StripExists(φᵢ)`. -/
def hatOf : Formula Voc → Formula Voc
  | .since _ _ φr => φr
  | .prev _ φ => φ
  | .agg _ _ _ _ φ => φ
  | χ => χ

/-- The variables `x̄ᵢȳ` to be guarded; `fv(φ̂ᵢ)` for an aggregation. -/
def gsOf (xs ys : List Voc.𝕍) : Formula Voc → Set Voc.𝕍
  | .since .. | .prev .. => {x | x ∈ xs}
  | .agg _ _ _ _ φ => φ.fv
  | _ => {x | x ∈ xs} ∪ {y | y ∈ ys}

/-- Temporal bodies and aggregations. -/
def TemporalOf : Formula Voc → Prop
  | .since .. | .prev .. | .agg .. => True
  | _ => False

/-- `cau(φᵢ)` -/
noncomputable def cauOf (φ : Formula Voc) : Formula Voc → Option (Formula Voc)
  | .since I _ φr => if 0 ∈ I then some φr else none
  | .prev .. | .agg .. => none
  | χ => if χ.Present then some φ else none

/-- `sup(φᵢ)` -/
noncomputable def supOf (φ : Formula Voc) : Formula Voc → Option (Formula Voc)
  | .since I φl φr => if 0 ∈ I then some (Formula.or φl φr) else some φl
  | .prev .. | .agg .. => none
  | χ => if χ.Present then some φ else none

/-- The conditions of l.2206–2221 on the let `d` and its capabilities `caps`,
    under the context `Γ'` of the earlier lets. -/
def CondOK (Ξ : RwSetting Voc) (Γ' : ACtx Voc) (d : LetDef Voc) (caps : Set Cap) : Prop :=
  (Cap.G ∈ caps ↔ Γ'.GSet Ξ .pos (gsOf d.xs (stripVars d.φ) (stripExists d.φ)) (hatOf (stripExists d.φ)) ∧
      ∀ I φl φr, stripExists d.φ = .since I φl φr → Γ'.GSet Ξ .neg {x | x ∈ d.xs} φl) ∧
  (TemporalOf (stripExists d.φ) → Cap.G ∈ caps) ∧
  (∀ ys ω ss gs φ, stripExists d.φ = .agg ys ω ss gs φ → Term.varsList ss ⊆ φ.fv) ∧
  (Cap.C ∈ caps ↔ Cap.G ∈ caps ∧ ∃ φc, cauOf d.φ (stripExists d.φ) = some φc ∧
      ∃ Δ, Typ Ξ Γ' .C φc Δ) ∧
  (Cap.S ∈ caps ↔ Cap.G ∈ caps ∧ ∃ φs, supOf d.φ (stripExists d.φ) = some φs ∧
      ∃ Δ, Typ Ξ Γ' .S φs Δ)

/-- `Γ` restricted to the names `N` (`Γ_{<i}`). -/
def ACtx.restrict (Γ : ACtx Voc) (N : Set Voc.ℰ) : ACtx Voc := fun e => if e ∈ N then Γ e else ∅

/-- The lets of `ℒ` are typed by `Γ` (l.2202–2224). -/
def LetsTyped (Ξ : RwSetting Voc) (Γ : ACtx Voc) (ℒ : List (LetDef Voc)) : Prop :=
  (∀ e, ¬ IsLet ℒ e → Γ e = ∅) ∧
  ∀ k (hk : k < ℒ.length), CondOK Ξ (Γ.restrict {e | IsLet (ℒ.take k) e}) ℒ[k] (Γ ℒ[k].e)

/-- **EF-MFOTL** (Definition A.1): `□φ`, in let-normal form `L`, is in EF-MFOTL
    with clause set `Δ` if, with lets typed by some `Γ`, `Γ ⊢ χ : ℂ ▷ Δ`
    (`χ = χ₁ ∧ … ∧ χ_n`). -/
def EFMFOTL (Ξ : RwSetting Voc) (L : LNF Voc) (Δ : Set (EClause Voc)) : Prop :=
  ∃ Γ : ACtx Voc, LetsTyped Ξ Γ L.lets ∧ Typ Ξ Γ .C (bigAnd L.chis) Δ

/-- Well-formedness of the let-normal form assumed by Theorem A.2
    (NOTES.md, N6): `fv(φᵢ) = x̄ᵢ`, the quantifiers `∃ȳ` of a body bind free
    variables, and the terms of an aggregation use variables of `φ̂ᵢ`. -/
def LNF.WFA (L : LNF Voc) : Prop :=
  (L.lets.map LetDef.e).Nodup ∧
  ∀ d ∈ L.lets, d.φ.fv = {x | x ∈ d.xs} ∧ (∀ y ∈ stripVars d.φ, y ∈ (stripExists d.φ).fv) ∧
    ∀ ys ω ss gs φ, stripExists d.φ = .agg ys ω ss gs φ → Term.varsList ss ⊆ φ.fv

end Paper
