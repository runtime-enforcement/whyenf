/-
  §4.3 Enforcement rewriting (main.tex l.1241–1374, Figure 5).
-/
import Paper.Guards

namespace Paper

variable {Voc : Vocabulary}

/-! ## Clauses -/

/-- Effects `ε` (l.1247): `e(t̄)`, `¬e(t̄)`, `◇_I e(t̄)`, `○…○ e(t̄)` (`n` times). -/
inductive Effect (Voc : Vocabulary) where
  | cau : Voc.ℰ → List (Term Voc) → Effect Voc
  | sup : Voc.ℰ → List (Term Voc) → Effect Voc
  | ev : Interval → Voc.ℰ → List (Term Voc) → Effect Voc
  | nexts : ℕ → Voc.ℰ → List (Term Voc) → Effect Voc

/-- A clause `θ ⇒ ε` with trigger `θ = (π, ψ)` (l.1245). -/
structure EClause (Voc : Vocabulary) where
  π : GDisj Voc
  ψ : Formula Voc
  ε : Effect Voc

/-- A set of sets of clauses `𝒞 = {C_k}_k` (l.1254). -/
abbrev CSet (Voc : Vocabulary) := Set (Set (EClause Voc))

/-- `𝒞[f] = {{f(π, ψ, ε) ∣ (π, ψ) ⇒ ε ∈ C} ∣ C ∈ 𝒞}` (l.1264). -/
def CSet.map (𝒞 : CSet Voc) (f : GDisj Voc → Formula Voc → Effect Voc → EClause Voc) : CSet Voc :=
  {D | ∃ C ∈ 𝒞, D = (fun c => f c.π c.ψ c.ε) '' C}

/-- `𝒞₁ ⊗ 𝒞₂ = {C₁ ∪ C₂ ∣ (C₁, C₂) ∈ 𝒞₁ × 𝒞₂}` (l.1265). -/
def CSet.tensor (𝒞₁ 𝒞₂ : CSet Voc) : CSet Voc := {D | ∃ C₁ ∈ 𝒞₁, ∃ C₂ ∈ 𝒞₂, D = C₁ ∪ C₂}

/-- `⨂ᵢ 𝒞ᵢ` -/
def CSet.bigTensor : List (CSet Voc) → CSet Voc
  | [] => {∅}
  | 𝒞 :: 𝒞s => 𝒞.tensor (bigTensor 𝒞s)

/-- `⋀ᵢ φᵢ` for a list of (at least two) conjuncts, nested to the right. -/
def bigAnd : List (Formula Voc) → Formula Voc
  | [] => .top
  | [φ] => φ
  | φ :: φs => .and φ (bigAnd φs)

/-- The trivial trigger component `⊤` for `π` is `{⊤}`. -/
def GDisj.top : GDisj Voc := [[]]

/-! ## Substitution of the canonical constant (rule `Ex^ℂ`) -/

def GAtom.subst (d : Voc.𝔻) (x : Voc.𝕍) : GAtom Voc → Option (GAtom Voc)
  | .pred p ts => some (.pred p (Term.substList d x ts))
  | .eq y c => if y = x then none else some (.eq y c)

def GDisj.subst (d : Voc.𝔻) (x : Voc.𝕍) (π : GDisj Voc) : Option (GDisj Voc) :=
  π.mapM (fun κ => κ.mapM (GAtom.subst d x))

def Effect.subst (d : Voc.𝔻) (x : Voc.𝕍) : Effect Voc → Effect Voc
  | .cau e ts => .cau e (Term.substList d x ts)
  | .sup e ts => .sup e (Term.substList d x ts)
  | .ev I e ts => .ev I e (Term.substList d x ts)
  | .nexts n e ts => .nexts n e (Term.substList d x ts)

/-! ## The setting of Figure 5 -/

/-- `Γ` maps let-bound event names to a triple `(g, c, s)` of booleans
    (guarded, causable, suppressable; l.1258–1261). -/
abbrev LetCtx (Voc : Vocabulary) := Voc.ℰ → Option (Bool × Bool × Bool)

/-- What Figure 5 takes as fixed:
    * `ℂ`, `𝕊`: the causable and suppressable event names (§2.3);
    * `base`: the base event names (not let-bound);
    * `cauN e`, `supN e`: the obligation event names `Cau_e`, `Sup_e` (l.1286–1289);
    * `zero`: the canonical value `0` of `Ex^ℂ` (l.1356). -/
structure RwSetting (Voc : Vocabulary) where
  Cau : Set Voc.ℰ
  Sup : Set Voc.ℰ
  base : Set Voc.ℰ
  cauN : Voc.ℰ → Voc.ℰ
  supN : Voc.ℰ → Voc.ℰ
  zero : Voc.𝔻

/-- `m_Γ`, the enumerable events of `Γ`: base events and lets with `g = ⊤`. -/
def RwSetting.m (Ξ : RwSetting Voc) (Γ : LetCtx Voc) : Set Voc.ℰ :=
  Ξ.base ∪ {p | ∃ c s, Γ p = some (true, c, s)}

/-- A formula is *present* if it contains no future operator (`○`, `◇`). -/
def Formula.Present : Formula Voc → Prop
  | .top => True
  | .pred _ _ => True
  | .eq _ _ => True
  | .neg φ => φ.Present
  | .and φ ψ => φ.Present ∧ ψ.Present
  | .ex _ φ => φ.Present
  | .next _ _ => False
  | .eventually _ _ => False
  | .prev _ φ => φ.Present
  | .since _ φ ψ => φ.Present ∧ ψ.Present
  | .letin _ _ φ ψ => φ.Present ∧ ψ.Present
  | .agg _ _ _ _ φ => φ.Present

/-- `m ⊢ (π, ψ) ⇝^p_x (π', ψ')` (§4.2): either every `κ ∈ π` binds `x` and
    `(π', ψ') = (π, ψ)`, or `m ⊢ ψ ⇝^p_{x} (π₀, ψ')` and
    `π' = {κ ∧ κ₀ ∣ κ ∈ π, κ₀ ∈ π₀}`. -/
inductive TGX (m : Set Voc.ℰ) (p : Pol) (x : Voc.𝕍) : GDisj Voc → Formula Voc → GDisj Voc →
    Formula Voc → Prop
  | bound {π ψ} : (∀ κ ∈ π, κ.Binds x) → TGX m p x π ψ π ψ
  | filter {π ψ π₀ ψ'} : GX m p {x} ψ π₀ ψ' → TGX m p x π ψ (π.prod π₀) ψ'

/-- `ℂ` / `𝕊` as the superscript of `↪`. -/
inductive Mode | C | S
  deriving DecidableEq

def Mode.flip : Mode → Mode
  | .C => .S
  | .S => .C

/-! ## Effects -/

namespace Effect

/-- The event `e` of an effect `e(t̄)`, `¬e(t̄)`, `◇_I e(t̄)`, `○…○ e(t̄)`. -/
def name : Effect Voc → Voc.ℰ
  | .cau e _ | .sup e _ | .ev _ e _ | .nexts _ e _ => e

/-- The arguments `t̄` of an effect. -/
def args : Effect Voc → List (Term Voc)
  | .cau _ ts | .sup _ ts | .ev _ _ ts | .nexts _ _ ts => ts

/-- The polarity `a ∈ {ℂ, 𝕊}` of an effect (l.1482).  `¬e(t̄)` is `𝕊`;
    `e(t̄)` and the deferred `◇_I e(t̄)`, `○…○ e(t̄)` are `ℂ`. -/
def pol : Effect Voc → Mode
  | .sup _ _ => .S
  | _ => .C

/-- The effect is deferred (`delay` or `next`, l.1490). -/
def deferred : Effect Voc → Bool
  | .ev .. | .nexts .. => true
  | _ => false

end Effect

/-- `C ≠ ∅ ∧ ∀ (π, ψ) ⇒ ε ∈ C. ∃ p, t̄. ε = p(t̄) ∧ π = ψ = ⊤` (`Fut` rules). -/
def Uncond (C : Set (EClause Voc)) : Prop :=
  ∀ c ∈ C, (∃ p ts, c.ε = .cau p ts) ∧ c.π = GDisj.top ∧ c.ψ = .top

/-- `○…○ φ` (`n` unbounded `○`). -/
def nextN (n : ℕ) (φ : Formula Voc) : Formula Voc := (Formula.next Interval.univ)^[n] φ

/-- The effect `ε` of an unconditional clause, `p(t̄)`, deferred by `f`. -/
def deferEffect (f : Voc.ℰ → List (Term Voc) → Effect Voc) : Effect Voc → Effect Voc
  | .cau p ts => f p ts
  | ε => ε

/-- `Γ ⊢ φ ↪^α 𝒞` (Figure 5). -/
inductive Rw (Ξ : RwSetting Voc) (Γ : LetCtx Voc) : Mode → Formula Voc → CSet Voc → Prop
  /-- `⊤^ℂ` -/
  | top : Rw Ξ Γ .C .top {∅}
  /-- `Ev^ℂ` -/
  | evC (e : Voc.ℰ) (ts : List (Term Voc)) : e ∈ Ξ.Cau →
      Rw Ξ Γ .C (.pred e ts) {{⟨GDisj.top, .top, .cau e ts⟩}}
  /-- `Ev^𝕊` -/
  | evS (e : Voc.ℰ) (ts : List (Term Voc)) : e ∈ Ξ.Sup →
      Rw Ξ Γ .S (.pred e ts) {{⟨[[.pred e ts]], .top, .sup e ts⟩}}
  /-- `Let^ℂ`: `Γ(e)₂ = ⊤` -/
  | letC (e : Voc.ℰ) (ts : List (Term Voc)) : (∃ g s, Γ e = some (g, true, s)) →
      Rw Ξ Γ .C (.pred e ts) {{⟨GDisj.top, .top, .cau (Ξ.cauN e) ts⟩}}
  /-- `Let^𝕊`: `Γ(e)₃ = ⊤` -/
  | letS (e : Voc.ℰ) (ts : List (Term Voc)) : (∃ g c, Γ e = some (g, c, true)) →
      Rw Ξ Γ .S (.pred e ts) {{⟨[[.pred e ts]], .top, .cau (Ξ.supN e) ts⟩}}
  /-- `Neg` -/
  | neg {α φ 𝒞} : Rw Ξ Γ α.flip φ 𝒞 → Rw Ξ Γ α (.neg φ) 𝒞
  /-- `And^𝕊` -/
  | andS (φs : List (Formula Voc)) (j : Fin φs.length) {𝒞 : CSet Voc} : 2 ≤ φs.length →
      Rw Ξ Γ .S φs[j] 𝒞 → (∀ i : Fin φs.length, i ≠ j → φs[i].Present) →
      Rw Ξ Γ .S (bigAnd φs)
        (𝒞.map fun π ψ ε => ⟨π, .and ψ (bigAnd ((List.finRange φs.length).filter (· ≠ j)
          |>.map fun i => φs[i])), ε⟩)
  /-- `And^ℂ` -/
  | andC (φs : List (Formula Voc)) (𝒞s : List (CSet Voc)) : 2 ≤ φs.length →
      List.Forall₂ (Rw Ξ Γ .C) φs 𝒞s → Rw Ξ Γ .C (bigAnd φs) (CSet.bigTensor 𝒞s)
  /-- `Ex^ℂ`: `𝒞[π, ψ, ε ↦ (π[0/x], ψ[0/x]) ⇒ ε[0/x]]`, when the
      substitutions are defined (NOTES.md, N2). -/
  | exC (x : Voc.𝕍) {φ 𝒞} : Rw Ξ Γ .C φ 𝒞 →
      (∀ C ∈ 𝒞, ∀ c ∈ C, (c.π.subst Ξ.zero x).isSome ∧ (c.ψ.subst Ξ.zero x).isSome) →
      Rw Ξ Γ .C (.ex x φ) (𝒞.map fun π ψ ε =>
        ⟨(π.subst Ξ.zero x).getD π, (ψ.subst Ξ.zero x).getD ψ, ε.subst Ξ.zero x⟩)
  /-- `Ex^𝕊` -/
  | exS (x : Voc.𝕍) {φ 𝒞} : Rw Ξ Γ .S φ 𝒞 →
      Rw Ξ Γ .S (.ex x φ)
        {D | ∃ C ∈ 𝒞, (∀ c ∈ C, ∃ π' ψ', TGX (Ξ.m Γ) .pos x c.π c.ψ π' ψ') ∧
          D = {c' | ∃ c ∈ C, TGX (Ξ.m Γ) .pos x c.π c.ψ c'.π c'.ψ ∧ c'.ε = c.ε}}
  /-- `Fut_◇^ℂ` -/
  | futEv (a b : ℕ) (h : (a : ℕ∞) ≤ b) {φ 𝒞} : Rw Ξ Γ .C φ 𝒞 → 1 ≤ b →
      Rw Ξ Γ .C (.eventually (Interval.icc a b h) φ)
        (CSet.map {C ∈ 𝒞 | C ≠ ∅ ∧ Uncond C} fun _ _ ε =>
          ⟨GDisj.top, .top, deferEffect (.ev (Interval.icc b b le_rfl)) ε⟩)
  /-- `Fut_○^ℂ` -/
  | futNext (b : ℕ∞) {φ 𝒞} : Rw Ξ Γ .C φ 𝒞 → 1 ≤ b →
      Rw Ξ Γ .C (.next (Interval.icc 0 b (by simp)) φ)
        (CSet.map {C ∈ 𝒞 | C ≠ ∅ ∧ Uncond C} fun _ _ ε =>
          ⟨GDisj.top, .top, deferEffect (.nexts 1) ε⟩)
  /-- `Fut_{○ⁿ}^ℂ` -/
  | futNextN (n : ℕ) {φ 𝒞} : Rw Ξ Γ .C φ 𝒞 → 1 ≤ n →
      Rw Ξ Γ .C (nextN n φ)
        (CSet.map {C ∈ 𝒞 | Uncond C} fun _ _ ε => ⟨GDisj.top, .top, deferEffect (.nexts n) ε⟩)

/-- `Γ ⊢ φ ↪^α`: the set of all `C ∈ 𝒞` with `Γ ⊢ φ ↪^α 𝒞` (§4.4). -/
def RwAll (Ξ : RwSetting Voc) (Γ : LetCtx Voc) (α : Mode) (φ : Formula Voc) : CSet Voc :=
  {C | ∃ 𝒞, Rw Ξ Γ α φ 𝒞 ∧ C ∈ 𝒞}

end Paper
