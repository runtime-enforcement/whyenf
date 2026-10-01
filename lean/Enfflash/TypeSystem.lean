/-
  EnfFlash formalization — a type system for the enforceable fragment
  (paper, Appendix "A type system for EF-MFOTL"), and its equivalence with
  the compilation rules.

  * `Typ S α φ Δ` (`Γ ⊢ φ : α ▷ Δ`): `φ` can be caused (`α = true`) or
    suppressed (`α = false`) by the clauses `Δ`.  It differs from the rewrite
    judgement `Rw` in producing a single clause set instead of a set of
    alternatives; the side condition of `∃^𝕊` is declarative by `gx_iff`.
  * `typ_iff_rw`: `Typ S α φ Δ` iff `Δ` is one of the alternatives produced
    by `Rw`.
  * `TypedLets`: typing of let bindings by capabilities `𝔾` (enumerable),
    `ℂ` (causable), `𝕊` (suppressable), with enumerability characterized by
    `Enum` (per-variable guardedness, `gxj_iff`).
  * `efmfotl_iff_compiles`: a formula (in let-normal form) is typable with
    clause set `Δ` iff the compilation rules (`TypeLet`'s guards, a valid
    realization, and the rewriting) succeed with the same clause set.
-/
import Enfflash.TableDeps

namespace Enfflash

variable {B D : Type}

/-! ## Typing of causation and suppression -/

/-- `Γ ⊢ φ : α ▷ Δ`. -/
inductive Typ (S : Sig B ℕ D) : Bool → Fm B ℕ D → List (Clause B ℕ D) → Prop
  | tt : Typ S true .tt []
  | evC {e ts} : S.cau e → Typ S true (.pred (.ev (.base e)) ts) [⟨0, Trigger.top, .cau (.base e) ts⟩]
  | evS {e ts} : S.sup e →
      Typ S false (.pred (.ev (.base e)) ts) [⟨0, ⟨[[.pred (.ev (.base e)) ts]], .tt⟩, .sup (.base e) ts⟩]
  | letC {p ts} : S.okC p → ts.length = S.ar p →
      Typ S true (.pred (.lp p) ts) [⟨0, Trigger.top, .cau (.cau p) ts⟩]
  | letS {p ts} : S.okS p → ts.length = S.ar p →
      Typ S false (.pred (.lp p) ts) [⟨0, ⟨[[.pred (.lp p) ts]], .tt⟩, .cau (.sup p) ts⟩]
  | neg {α φ Δ} : Typ S (!α) φ Δ → Typ S α (.neg φ) Δ
  | andC {φ ψ Δ₁ Δ₂} : Typ S true φ Δ₁ → Typ S true ψ Δ₂ → Typ S true (.conj φ ψ) (Δ₁ ++ Δ₂)
  | andSL {φ ψ Δ} : Typ S false φ Δ → ψ.present →
      Typ S false (.conj φ ψ) (Δ.map (Clause.addFilter ψ))
  | andSR {φ ψ Δ} : Typ S false ψ Δ → φ.present →
      Typ S false (.conj φ ψ) (Δ.map (Clause.addFilter φ))
  | exC {φ Δ} : Typ S true φ Δ → Typ S true (.ex φ) (Δ.map (Clause.substCtx (instS 0 S.d₀)))
  /-- `x` must be guarded in every trigger (`gx_iff`); `Δ'` extracts these guards. -/
  | exS {φ Δ Δ'} : Typ S false φ Δ → List.Forall₂ (ExGuard S.enum) Δ Δ' → Typ S false (.ex φ) Δ'
  | futEv {a b φ Δ} : Typ S true φ Δ → a ≤ b → 1 ≤ b → Δ ≠ [] → (∀ c ∈ Δ, c.simple) →
      Typ S true (.ev a b φ) (Δ.map (Clause.mapCau (.later b)))
  | futNx1 {b φ Δ} : Typ S true φ Δ → 1 ≤ b → Δ ≠ [] → (∀ c ∈ Δ, c.simple) →
      Typ S true (.nx 0 (some b) φ) (Δ.map (Clause.mapCau (.next 1 true)))
  | futNxU {n φ Δ} : Typ S true φ Δ → 1 ≤ n → (∀ c ∈ Δ, c.simple) →
      Typ S true (nxU n φ) (Δ.map (Clause.mapCau (.next n false)))

/-- The side condition of `∃^𝕊`, declaratively: the variable is guarded in
    every trigger. -/
theorem exS_side_iff {m : Pr B ℕ → Prop} (Δ : List (Clause B ℕ D)) :
    (∃ Δ', List.Forall₂ (ExGuard m) Δ Δ') ↔
      ∀ c ∈ Δ, c.trig.guards.bindsAll c.nloc ∨ Grd m c.nloc true c.trig.filter := by
  induction Δ with
  | nil => exact ⟨fun _ => by simp, fun _ => ⟨[], .nil⟩⟩
  | cons c Δ ih =>
    constructor
    · rintro ⟨Δ', hf⟩ c' hc'
      cases hf with
      | cons hg hrest =>
        obtain ⟨_, _, hgx⟩ := hg
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact gx_iff.1 ⟨_, _, hgx⟩
        · exact ih.1 ⟨_, hrest⟩ c' hc'
    · intro h
      obtain ⟨π', φ', hgx⟩ := gx_iff.2 (h c (List.mem_cons_self ..))
      obtain ⟨Δ', hΔ'⟩ := ih.2 fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
      exact ⟨⟨c.nloc + 1, ⟨π', φ'⟩, c.eff⟩ :: Δ', .cons ⟨rfl, rfl, hgx⟩ hΔ'⟩

theorem mem_prodCS {CS₁ CS₂ : List (List (Clause B ℕ D))} {C : List (Clause B ℕ D)} :
    C ∈ prodCS CS₁ CS₂ ↔ ∃ C₁ ∈ CS₁, ∃ C₂ ∈ CS₂, C = C₁ ++ C₂ := by
  simp only [prodCS, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨C₁, h₁, C₂, h₂, rfl⟩; exact ⟨C₁, h₁, C₂, h₂, rfl⟩
  · rintro ⟨C₁, h₁, C₂, h₂, rfl⟩; exact ⟨C₁, h₁, C₂, h₂, rfl⟩

theorem typ_of_rw {S : Sig B ℕ D} {α : Bool} {φ : Fm B ℕ D} {CS : List (List (Clause B ℕ D))}
    (h : Rw S α φ CS) : ∀ Δ ∈ CS, Typ S α φ Δ := by
  induction h with
  | tt => intro Δ h; simp at h; subst h; exact .tt
  | evC hc => intro Δ h; simp at h; subst h; exact .evC hc
  | evS hs => intro Δ h; simp at h; subst h; exact .evS hs
  | letC ho hl => intro Δ h; simp at h; subst h; exact .letC ho hl
  | letS ho hl => intro Δ h; simp at h; subst h; exact .letS ho hl
  | neg _ ih => exact fun Δ h => .neg (ih Δ h)
  | andC _ _ ih₁ ih₂ =>
    intro Δ h
    obtain ⟨C₁, h₁, C₂, h₂, rfl⟩ := mem_prodCS.1 h
    exact .andC (ih₁ C₁ h₁) (ih₂ C₂ h₂)
  | andSL _ hp ih => intro Δ h; obtain ⟨C, hC, rfl⟩ := List.mem_map.1 h; exact .andSL (ih C hC) hp
  | andSR _ hp ih => intro Δ h; obtain ⟨C, hC, rfl⟩ := List.mem_map.1 h; exact .andSR (ih C hC) hp
  | exC _ ih => intro Δ h; obtain ⟨C, hC, rfl⟩ := List.mem_map.1 h; exact .exC (ih C hC)
  | exS _ hCS ih =>
    intro Δ h; obtain ⟨C, hC, hf⟩ := hCS Δ h; exact .exS (ih C hC) hf
  | futEv _ hab hb hCS ih =>
    intro Δ h; obtain ⟨C, hC, hne, hs, rfl⟩ := hCS Δ h; exact .futEv (ih C hC) hab hb hne hs
  | futNx1 _ hb hCS ih =>
    intro Δ h; obtain ⟨C, hC, hne, hs, rfl⟩ := hCS Δ h; exact .futNx1 (ih C hC) hb hne hs
  | futNxU _ hn hCS ih =>
    intro Δ h; obtain ⟨C, hC, hs, rfl⟩ := hCS Δ h; exact .futNxU (ih C hC) hn hs

theorem rw_of_typ {S : Sig B ℕ D} {α : Bool} {φ : Fm B ℕ D} {Δ : List (Clause B ℕ D)}
    (h : Typ S α φ Δ) : ∃ CS, Rw S α φ CS ∧ Δ ∈ CS := by
  induction h with
  | tt => exact ⟨_, .tt, List.mem_singleton_self _⟩
  | evC hc => exact ⟨_, .evC hc, List.mem_singleton_self _⟩
  | evS hs => exact ⟨_, .evS hs, List.mem_singleton_self _⟩
  | letC ho hl => exact ⟨_, .letC ho hl, List.mem_singleton_self _⟩
  | letS ho hl => exact ⟨_, .letS ho hl, List.mem_singleton_self _⟩
  | neg _ ih => obtain ⟨CS, h, hm⟩ := ih; exact ⟨CS, .neg h, hm⟩
  | andC _ _ ih₁ ih₂ =>
    obtain ⟨CS₁, h₁, m₁⟩ := ih₁; obtain ⟨CS₂, h₂, m₂⟩ := ih₂
    exact ⟨_, .andC h₁ h₂, mem_prodCS.2 ⟨_, m₁, _, m₂, rfl⟩⟩
  | andSL _ hp ih => obtain ⟨CS, h, hm⟩ := ih; exact ⟨_, .andSL h hp, List.mem_map_of_mem hm⟩
  | andSR _ hp ih => obtain ⟨CS, h, hm⟩ := ih; exact ⟨_, .andSR h hp, List.mem_map_of_mem hm⟩
  | exC _ ih => obtain ⟨CS, h, hm⟩ := ih; exact ⟨_, .exC h, List.mem_map_of_mem hm⟩
  | @exS φ Δ Δ' _ hf ih =>
    obtain ⟨CS, h, hm⟩ := ih
    exact ⟨[Δ'], .exS h fun C' hC' => by simp at hC'; subst hC'; exact ⟨Δ, hm, hf⟩,
      List.mem_singleton_self _⟩
  | @futEv a b φ Δ _ hab hb hne hs ih =>
    obtain ⟨CS, h, hm⟩ := ih
    exact ⟨_, .futEv h hab hb fun C' hC' => by
      simp at hC'; subst hC'; exact ⟨Δ, hm, hne, hs, rfl⟩, List.mem_singleton_self _⟩
  | @futNx1 b φ Δ _ hb hne hs ih =>
    obtain ⟨CS, h, hm⟩ := ih
    exact ⟨_, .futNx1 h hb fun C' hC' => by
      simp at hC'; subst hC'; exact ⟨Δ, hm, hne, hs, rfl⟩, List.mem_singleton_self _⟩
  | @futNxU n φ Δ _ hn hs ih =>
    obtain ⟨CS, h, hm⟩ := ih
    exact ⟨_, .futNxU h hn fun C' hC' => by
      simp at hC'; subst hC'; exact ⟨Δ, hm, hs, rfl⟩, List.mem_singleton_self _⟩

/-- **The typing of causation/suppression coincides with the rewriting.** -/
theorem typ_iff_rw {S : Sig B ℕ D} {α : Bool} {φ : Fm B ℕ D} {Δ : List (Clause B ℕ D)} :
    Typ S α φ Δ ↔ ∃ CS, Rw S α φ CS ∧ Δ ∈ CS :=
  ⟨rw_of_typ, fun ⟨_, h, hm⟩ => typ_of_rw h Δ hm⟩

/-! ## Typing of let bindings -/

/-- Capabilities of the lets: enumerable (`𝔾`), causable (`ℂ`),
    suppressable (`𝕊`). -/
structure Caps where
  G : ℕ → Prop
  C : ℕ → Prop
  S : ℕ → Prop

/-- Enumerable predicates: base events and enumerable lets. -/
def enumCaps (κ : Caps) : Pr B ℕ → Prop
  | .ev _ => True
  | .lp q => κ.G q

/-- The rewriting signature for a scope of lets. -/
def sigOf (S₀ : Sig B ℕ D) (en : Pr B ℕ → Prop) (okC okS : ℕ → Prop) : Sig B ℕ D :=
  { S₀ with enum := en, okC := okC, okS := okS }

/-- `Γ ⊢ body :: τ` for every let: `𝔾` requires the value-producing operand to
    be enumerable (after stripping existentials; for an aggregation, in all
    variables except the results) and, for a since, its left operand to be
    enumerable in negative polarity; temporal lets and aggregations are
    enumerable, and the terms of an aggregation only read enumerated
    variables; `ℂ`/`𝕊` require an enumerable let whose causation/suppression
    target is typable in the scope of the earlier lets. -/
structure TypedLets (S₀ : Sig B ℕ D) (Γ : List (LetDef B ℕ D)) (κ : Caps) : Prop where
  enum : ∀ p (d : LetDef B ℕ D), Γ[p]? = some d → κ.G p →
    ∃ φ, d.gop = some φ ∧ Enum (enumCaps κ) d.gvars true φ
  removal : ∀ p (d : LetDef B ℕ D) a b φl φr, Γ[p]? = some d → d.body = .since a b φl φr →
    κ.G p → Enum (enumCaps κ) (List.range d.arity) false φl
  temporal : ∀ p (d : LetDef B ℕ D), Γ[p]? = some d →
    (∀ a b φl φr, d.body = .since a b φl φr → κ.G p) ∧ (∀ a b φ, d.body = .prev a b φ → κ.G p) ∧
    (∀ k ω ts ys φ, d.body = .agg k ω ts ys φ → κ.G p)
  aggTerms : ∀ (p : ℕ) (d : LetDef B ℕ D) k ω ts ys φ, Γ[p]? = some d →
    d.body = .agg k ω ts ys φ → ∀ t ∈ ts, t.WF ∧ ∀ x ∈ t.supp, x ∈ d.gvars
  undef : ∀ p, Γ[p]? = none → ¬ κ.G p ∧ ¬ κ.C p ∧ ¬ κ.S p
  cau : ∀ p, κ.C p → κ.G p ∧ ∃ d φ Δ, Γ[p]? = some d ∧ d.arity = S₀.ar p ∧
    d.body.cauTarget = some φ ∧
    Typ (sigOf S₀ (enumCaps κ) (fun q => q < p ∧ κ.C q) (fun q => q < p ∧ κ.S q)) true φ Δ
  sup : ∀ p, κ.S p → κ.G p ∧ ∃ d φ Δ, Γ[p]? = some d ∧ d.arity = S₀.ar p ∧
    d.body.supTarget = some φ ∧
    Typ (sigOf S₀ (enumCaps κ) (fun q => q < p ∧ κ.C q) (fun q => q < p ∧ κ.S q)) false φ Δ

/-- **`EF-MFOTL`**: the let-normal form `(χ, Γ)` of `φ` is typable, `Γ` with
    some capabilities and `χ` as causable with clause set `Δ`. -/
def EFMFOTL (S₀ : Sig B ℕ D) (φ : MF B D) (Δ : List (Clause B ℕ D)) : Prop :=
  ∃ κ : Caps, TypedLets S₀ (lnf φ).2 κ ∧ Typ (sigOf S₀ (enumCaps κ) κ.C κ.S) true (lnf φ).1 Δ

/-- A successful run of the compilation rules for `□φ` with candidate
    clause set `Δ`: `TypeLet` computes guards `gd` for the lets, a valid
    realization `R` provides the clauses of causable and suppressable (hence
    guardable) lets, and the rewriting of `χ` yields the alternatives `CS`,
    among them `Δ`. -/
structure Compilation (S₀ : Sig B ℕ D) (φ : MF B D) (Δ : List (Clause B ℕ D)) where
  gd : ℕ → Option (Guards B ℕ D)
  R : Real B ℕ D
  CS : List (List (Clause B ℕ D))
  guards : LetGuards (lnf φ).2 gd
  guardsDef : ∀ p, (gd p).isSome → ((lnf φ).2[p]?).isSome
  cauGuarded : ∀ p, R.cauCl p ≠ none → (gd p).isSome
  supGuarded : ∀ p, R.supCl p ≠ none → (gd p).isSome
  valid : R.Valid (sigOf S₀ (enumOf gd) (fun _ => False) (fun _ => False)) (envOf (lnf φ).2) (· < ·)
  rewrite : Rw (R.scope (sigOf S₀ (enumOf gd) (fun _ => False) (fun _ => False)) (fun _ => True))
    true (lnf φ).1 CS
  choice : Δ ∈ CS

/-- The compilation rules succeed on `□φ` with candidate clause set `Δ`. -/
def Compiles (S₀ : Sig B ℕ D) (φ : MF B D) (Δ : List (Clause B ℕ D)) : Prop :=
  Nonempty (Compilation S₀ φ Δ)

/-! ## Equivalence -/

theorem Real.scope_sigOf (R : Real B ℕ D) (S₀ : Sig B ℕ D) (en : Pr B ℕ → Prop) (ok : ℕ → Prop) :
    R.scope (sigOf S₀ en (fun _ => False) (fun _ => False)) ok =
      sigOf S₀ en (fun q => ok q ∧ R.cauCl q ≠ none) (fun q => ok q ∧ R.supCl q ≠ none) := rfl

theorem sigOf_congr {S₀ : Sig B ℕ D} {en en' : Pr B ℕ → Prop} {c c' s s' : ℕ → Prop}
    (he : ∀ p, en p ↔ en' p) (hc : ∀ q, c q ↔ c' q) (hs : ∀ q, s q ↔ s' q) :
    sigOf S₀ en c s = sigOf S₀ en' c' s' := by
  have h1 : en = en' := funext fun p => propext (he p)
  have h2 : c = c' := funext fun q => propext (hc q)
  have h3 : s = s' := funext fun q => propext (hs q)
  subst h1 h2 h3; rfl

open Classical in
/-- **The type system characterizes the compilable fragment.** -/
theorem efmfotl_iff_compiles (S₀ : Sig B ℕ D) (φ : MF B D) (Δ : List (Clause B ℕ D)) :
    EFMFOTL S₀ φ Δ ↔ Compiles S₀ φ Δ := by
  set Γ := (norm φ [] []).2
  set χ := (norm φ [] []).1
  constructor
  · -- from a typing to a compilation
    rintro ⟨κ, hL, hT⟩
    -- guards from enumerability
    let P : ℕ → Guards B ℕ D → Prop := fun p π => κ.G p ∧ ∃ d φ₀ φ', Γ[p]? = some d ∧
      d.gop = some φ₀ ∧ GXJ (enumCaps κ) d.gvars true φ₀ π φ'
    let gd : ℕ → Option (Guards B ℕ D) := fun p =>
      if h : ∃ π, P p π then some (Classical.choose h) else none
    have hgdG : ∀ p, (gd p).isSome ↔ κ.G p := by
      intro p
      constructor
      · intro h
        by_cases hex : ∃ π, P p π
        · exact hex.choose_spec.1
        · simp [gd, dif_neg hex] at h
      · intro hG
        rcases hd : Γ[p]? with _ | d
        · exact absurd hG (hL.undef p hd).1
        obtain ⟨φ₀, hvo, hen⟩ := hL.enum p d hd hG
        obtain ⟨π, φ', hj⟩ := gxj_iff.2 hen
        have hex : ∃ π, P p π := ⟨π, hG, d, φ₀, φ', hd, hvo, hj⟩
        simp [gd, dif_pos hex]
    have hgdP : ∀ p π, gd p = some π → P p π := by
      intro p π h
      by_cases hex : ∃ π, P p π
      · simp only [gd, dif_pos hex, Option.some.injEq] at h; subst h; exact hex.choose_spec
      · simp [gd, dif_neg hex] at h
    have hen : ∀ p, enumOf gd p ↔ enumCaps κ p := by
      intro p; cases p <;> simp [enumOf, enumCaps, hgdG]
    have hm' : enumOf gd = enumCaps κ := funext fun p => propext (hen p)
    -- realizations from the let typings
    let R : Real B ℕ D :=
      ⟨fun p => if h : κ.C p then some (Classical.choose (Classical.choose_spec
          (Classical.choose_spec (hL.cau p h).2))) else none,
       fun p => if h : κ.S p then some (Classical.choose (Classical.choose_spec
          (Classical.choose_spec (hL.sup p h).2))) else none⟩
    have hRC : ∀ q, R.cauCl q ≠ none ↔ κ.C q := by
      intro q; by_cases h : κ.C q <;> simp [R, h]
    have hRS : ∀ q, R.supCl q ≠ none ↔ κ.S q := by
      intro q; by_cases h : κ.S q <;> simp [R, h]
    have hsig : ∀ ok : ℕ → Prop, R.scope (sigOf S₀ (enumOf gd) (fun _ => False) (fun _ => False)) ok =
        sigOf S₀ (enumCaps κ) (fun q => ok q ∧ κ.C q) (fun q => ok q ∧ κ.S q) := fun ok =>
      (Real.scope_sigOf R S₀ _ ok).trans
        (sigOf_congr hen (fun q => and_congr_right fun _ => hRC q) (fun q => and_congr_right fun _ => hRS q))
    obtain ⟨CS, hrw, hm⟩ := rw_of_typ hT
    refine ⟨⟨gd, R, CS, ⟨?_, ?_, ?_, hL.aggTerms⟩, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, hm⟩⟩
    · -- guards
      intro p d π hd hgp
      obtain ⟨-, d', φ₀, φ', hd', hvo, hj⟩ := hgdP p π hgp
      rw [hd] at hd'; cases hd'
      exact ⟨φ₀, φ', hvo, by rw [hm']; exact hj⟩
    · intro p d a b φl φr hd hb hs
      rw [hm']; exact hL.removal p d a b φl φr hd hb ((hgdG p).1 hs)
    · intro p d hd
      exact ⟨fun a b φl φr hb => (hgdG p).2 ((hL.temporal p d hd).1 a b φl φr hb),
        fun a b φ hb => (hgdG p).2 ((hL.temporal p d hd).2.1 a b φ hb),
        fun k ω ts ys φ hb => (hgdG p).2 ((hL.temporal p d hd).2.2 k ω ts ys φ hb)⟩
    · intro p hs
      rcases hd : Γ[p]? with _ | d
      · exact absurd ((hgdG p).1 hs) (hL.undef p hd).1
      · rfl
    · intro p h; exact (hgdG p).2 (hL.cau p ((hRC p).1 h)).1
    · intro p h; exact (hgdG p).2 (hL.sup p ((hRS p).1 h)).1
    · -- causation realizations
      intro p C hC
      have hCp : κ.C p := (hRC p).1 (by rw [hC]; simp)
      simp only [R, dif_pos hCp, Option.some.injEq] at hC
      have hspec := Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec (hL.cau p hCp).2))
      obtain ⟨hd', har', ht', hty'⟩ := hspec
      subst hC
      obtain ⟨CS', hrw', hm''⟩ := rw_of_typ hty'
      refine ⟨_, _, CS', hd', ?_, ht', ?_, hm''⟩
      · simpa [sigOf] using har'
      · rw [hsig]; exact hrw'
    · intro p C hC
      have hSp : κ.S p := (hRS p).1 (by rw [hC]; simp)
      simp only [R, dif_pos hSp, Option.some.injEq] at hC
      have hspec := Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec (hL.sup p hSp).2))
      obtain ⟨hd', har', ht', hty'⟩ := hspec
      subst hC
      obtain ⟨CS', hrw', hm''⟩ := rw_of_typ hty'
      refine ⟨_, _, CS', hd', ?_, ht', ?_, hm''⟩
      · simpa [sigOf] using har'
      · rw [hsig]; exact hrw'
    · rw [hsig]
      have : sigOf S₀ (enumCaps κ) (fun q => True ∧ κ.C q) (fun q => True ∧ κ.S q) =
          sigOf S₀ (enumCaps κ) κ.C κ.S := sigOf_congr (fun _ => Iff.rfl) (fun _ => iff_of_eq (true_and _))
            (fun _ => iff_of_eq (true_and _))
      rw [this]; exact hrw
  · -- from a compilation to a typing
    rintro ⟨⟨gd, R, CS, hg, hdef, hRC, hRS, hV, hrw, hm⟩⟩
    let κ : Caps := ⟨fun p => (gd p).isSome, fun p => R.cauCl p ≠ none, fun p => R.supCl p ≠ none⟩
    have hen : enumOf gd = enumCaps κ := by funext p; cases p <;> rfl
    have hsig : ∀ ok : ℕ → Prop, R.scope (sigOf S₀ (enumOf gd) (fun _ => False) (fun _ => False)) ok =
        sigOf S₀ (enumCaps κ) (fun q => ok q ∧ κ.C q) (fun q => ok q ∧ κ.S q) := fun ok => by
      rw [Real.scope_sigOf, hen]
    refine ⟨κ, ⟨?_, ?_, ?_, hg.aggTerms, ?_, ?_, ?_⟩, ?_⟩
    · intro p d hd hG
      obtain ⟨π, hπ⟩ := Option.isSome_iff_exists.1 hG
      obtain ⟨φ₀, φ', hvo, hj⟩ := hg.guards p d π hd hπ
      exact ⟨φ₀, hvo, by rw [← hen]; exact gxj_iff.1 ⟨_, _, hj⟩⟩
    · intro p d a b φl φr hd hb hG
      rw [← hen]; exact hg.removal p d a b φl φr hd hb hG
    · intro p d hd; exact hg.temporal p d hd
    · intro p hd
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have := hdef p h; rw [hd] at this; exact Bool.false_ne_true this
      · have := hdef p (hRC p h); rw [hd] at this; exact Bool.false_ne_true this
      · have := hdef p (hRS p h); rw [hd] at this; exact Bool.false_ne_true this
    · intro p hC
      refine ⟨hRC p hC, ?_⟩
      obtain ⟨C, hCp⟩ := Option.ne_none_iff_exists'.1 hC
      obtain ⟨d, φ₀, CS', hd, har, ht, hrw', hm'⟩ := hV.cau p C hCp
      refine ⟨d, φ₀, C, hd, by simpa [sigOf] using har, ht, ?_⟩
      rw [← hsig]; exact typ_of_rw hrw' C hm'
    · intro p hS
      refine ⟨hRS p hS, ?_⟩
      obtain ⟨C, hCp⟩ := Option.ne_none_iff_exists'.1 hS
      obtain ⟨d, φ₀, CS', hd, har, ht, hrw', hm'⟩ := hV.sup p C hCp
      refine ⟨d, φ₀, C, hd, by simpa [sigOf] using har, ht, ?_⟩
      rw [← hsig]; exact typ_of_rw hrw' C hm'
    · have := hsig (fun _ => True)
      rw [this] at hrw
      have h2 : sigOf S₀ (enumCaps κ) (fun q => True ∧ κ.C q) (fun q => True ∧ κ.S q) =
          sigOf S₀ (enumCaps κ) κ.C κ.S := sigOf_congr (fun _ => Iff.rfl) (fun _ => iff_of_eq (true_and _))
            (fun _ => iff_of_eq (true_and _))
      rw [h2] at hrw
      exact typ_of_rw hrw Δ hm

end Enfflash
