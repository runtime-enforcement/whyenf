/-
  EnfFlash formalization — the compilation algorithm (paper, Algorithms 3
  and 4: `Generate`, `TypeLet`, `Compile`) as functions, with proofs that
  their results satisfy the compilation rules.

  * `gx`, `gxj`: guard extraction (`↝`, Figures 4 and 5) as a search;
    `gx_sound`, `gxj_sound`: a result is a derivation of `GX`/`GXJ`.
  * `rw`: the rewriting `Γ ⊢ φ ↪^α 𝒞` (Figure 6) as a function returning the
    candidate clause sets; `rw_sound`: a result is a derivation of `Rw`.
  * `typeLets`: `TypeLet`, one pass over the lets in let order: the guards
    of each let (in the scope of the earlier ones), then its causation and
    suppression clauses (rewriting its targets in the scope of the earlier
    lets); `compilation`: a `Compilation` for every candidate clause set of
    the enforced formula.
  * `compile`: `Compile(Γ, R, ≺)`: the compiled programs (one per candidate
    clause set), with the rules sectioned along the SCCs of the EDG;
    `compile_sound`: every program it returns whose checks pass is a sound
    enforcer.
  * `enfflash`: the whole pipeline (compile, check, run the first program
    that passes the checks); `enforcement_correct` (the end-to-end
    theorem): every enforcer it returns is sound.

  The functions are definitions, not executable code (`noncomputable`):
  function terms are semantic, so term equality and well-formedness are not
  decidable, and the signature's capabilities are propositions; these are
  decided classically.  The algorithm is deterministic: where the rules
  allow a choice, it takes the first option (e.g. the left conjunct for
  guards and suppression, the first candidate as realization of a let).
-/
import Enfflash.EndToEnd

set_option autoImplicit false

namespace Enfflash

open Classical

universe u

section Generic
variable {B L D : Type u}

/-! ## Guard extraction (Figures 4 and 5) -/

section
variable (m : Pr B L → Prop)

/-- `(π, φ) ↝_x (π', φ')`: extract guards for `x` from `φ`, adding them to
    `π` (Figure 4).  Existing guards binding `x` are kept; in a positive
    conjunction the left conjunct is tried first. -/
noncomputable def gx (x : ℕ) : Bool → Guards B L D → Fm B L D → Option (Guards B L D × Fm B L D)
  | p, π, φ =>
    if π.bindsAll x then some (π, φ) else
    match p, φ with
    | false, .tt => some ([], .tt)
    | true, .pred q ts => if m q ∧ Term.var x ∈ ts then some (π.addAtom (.pred q ts), .tt) else none
    | true, .eq (.var y) (.const d) => if y = x then some (π.addAtom (.eq (.var x) d), .tt) else none
    | p, .neg φ => (gx x (!p) π φ).map fun r => (r.1, .neg r.2)
    | true, .conj φ ψ =>
      match gx x true π φ with
      | some r => some (r.1, .conj r.2 ψ)
      | none => (gx x true π ψ).map fun r => (r.1, .conj φ r.2)
    | false, .conj φ ψ =>
      match gx x false π φ, gx x false π ψ with
      | some r₁, some r₂ => some (r₁.1 ++ r₂.1, .conj (impFm r₁.1 r₁.2) (impFm r₂.1 r₂.2))
      | _, _ => none
    | _, _ => none

theorem gx_sound (x : ℕ) :
    ∀ (φ : Fm B L D) (p : Bool) (π π' : Guards B L D) (φ' : Fm B L D),
      gx m x p π φ = some (π', φ') → GX m x p π φ π' φ' := by
  intro φ
  induction φ with
  | tt =>
    intro p π π' φ' h
    unfold gx at h
    split_ifs at h with hb
    · cases h; exact .grd hb
    · cases p <;> simp at h
      obtain ⟨rfl, rfl⟩ := h; exact .vacNeg
  | pred q ts =>
    intro p π π' φ' h
    unfold gx at h
    split_ifs at h with hb
    · cases h; exact .grd hb
    · cases p
      · simp at h
      · simp only at h
        split_ifs at h with hq
        cases h; exact .pred hq.1 hq.2
  | eq t u =>
    intro p π π' φ' h
    unfold gx at h
    split_ifs at h with hb
    · cases h; exact .grd hb
    · cases p
      · simp at h
      · cases t <;> cases u <;> simp at h
        obtain ⟨rfl, rfl, rfl⟩ := h; exact .eq
  | neg φ ih =>
    intro p π π' φ' h
    unfold gx at h
    split_ifs at h with hb
    · cases h; exact .grd hb
    · cases p <;>
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨π₁, φ₁⟩, h₁, h₂⟩ := h
        cases h₂; exact .neg (ih _ _ _ _ h₁)
  | conj φ ψ ih₁ ih₂ =>
    intro p π π' φ' h
    unfold gx at h
    split_ifs at h with hb
    · cases h; exact .grd hb
    · cases p
      · simp only at h
        split at h
        · rename_i r₁ r₂ h₁ h₂
          cases h
          exact .andNeg (ih₁ _ _ _ _ h₁) (ih₂ _ _ _ _ h₂)
        · simp at h
      · simp only at h
        split at h
        · rename_i r h₁
          cases h; exact .andL (ih₁ _ _ _ _ h₁)
        · simp only [Option.map_eq_some_iff] at h
          obtain ⟨⟨π₁, ψ₁⟩, h₁, h₂⟩ := h
          cases h₂; exact .andR (ih₂ _ _ _ _ h₁)
  | ex φ =>
    intro p π π' φ' h
    unfold gx at h
    split_ifs at h with hb
    · cases h; exact .grd hb
    · cases p <;> simp at h
  | ev a b φ =>
    intro p π π' φ' h
    unfold gx at h
    split_ifs at h with hb
    · cases h; exact .grd hb
    · cases p <;> simp at h
  | nx a b φ =>
    intro p π π' φ' h
    unfold gx at h
    split_ifs at h with hb
    · cases h; exact .grd hb
    · cases p <;> simp at h

/-- `Guards^m_X(φ)`: joint guard extraction for the variables `X`
    (Figure 5).  In a positive conjunction, the variables guardable in the
    left conjunct are guarded there, the others in the right one. -/
noncomputable def gxj : List ℕ → Bool → Fm B L D → Option (Guards B L D × Fm B L D)
  | X, p, φ =>
    if X = [] then some ([[]], φ) else
    match p, φ with
    | false, .tt => some ([], .tt)
    | true, .pred q ts =>
      if m q ∧ ∀ x ∈ X, Term.var x ∈ ts then some ([[.pred q ts]], .tt) else none
    | true, .eq (.var y) (.const d) =>
      if ∀ x ∈ X, x = y then some ([[.eq (.var y) d]], .tt) else none
    | p, .neg φ => (gxj X (!p) φ).map fun r => (r.1, .neg r.2)
    | true, .conj φ ψ =>
      let X₁ := X.filter fun x => (gxj [x] true φ).isSome
      let X₂ := X.filter fun x => !(gxj [x] true φ).isSome
      match gxj X₁ true φ, gxj X₂ true ψ with
      | some r₁, some r₂ => some (Guards.prod r₁.1 r₂.1, .conj r₁.2 r₂.2)
      | _, _ => none
    | false, .conj φ ψ =>
      match gxj X false φ, gxj X false ψ with
      | some r₁, some r₂ => some (r₁.1 ++ r₂.1, .conj (impFm r₁.1 r₁.2) (impFm r₂.1 r₂.2))
      | _, _ => none
    | _, _ => none

theorem gxj_sound :
    ∀ (φ : Fm B L D) (X : List ℕ) (p : Bool) (π : Guards B L D) (φ' : Fm B L D),
      gxj m X p φ = some (π, φ') → GXJ m X p φ π φ' := by
  intro φ
  induction φ with
  | tt =>
    intro X p π φ' h
    unfold gxj at h
    split_ifs at h with hX
    · cases h; subst hX; exact .none
    · cases p <;> simp at h
      obtain ⟨rfl, rfl⟩ := h; exact .vac
  | pred q ts =>
    intro X p π φ' h
    unfold gxj at h
    split_ifs at h with hX
    · cases h; subst hX; exact .none
    · cases p
      · simp at h
      · simp only at h
        split_ifs at h with hq
        cases h; exact .pred hq.1 hq.2
  | eq t u =>
    intro X p π φ' h
    unfold gxj at h
    split_ifs at h with hX
    · cases h; subst hX; exact .none
    · cases p
      · simp at h
      · cases t <;> cases u <;> simp at h
        obtain ⟨hy, rfl, rfl⟩ := h; exact .eq hy
  | neg φ ih =>
    intro X p π φ' h
    unfold gxj at h
    split_ifs at h with hX
    · cases h; subst hX; exact .none
    · cases p <;>
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨⟨π₁, φ₁⟩, h₁, h₂⟩ := h
        cases h₂; exact .neg (ih _ _ _ _ h₁)
  | conj φ ψ ih₁ ih₂ =>
    intro X p π φ' h
    unfold gxj at h
    split_ifs at h with hX
    · cases h; subst hX; exact .none
    · cases p
      · simp only at h
        split at h
        · rename_i r₁ r₂ h₁ h₂
          cases h; exact .andNeg (ih₁ _ _ _ _ h₁) (ih₂ _ _ _ _ h₂)
        · simp at h
      · simp only at h
        split at h
        · rename_i r₁ r₂ h₁ h₂
          cases h
          refine .andPos (ih₁ _ _ _ _ h₁) (ih₂ _ _ _ _ h₂) fun x hx => ?_
          by_cases hs : (gxj m [x] true φ).isSome
          · exact Or.inl (List.mem_filter.2 ⟨hx, hs⟩)
          · exact Or.inr (List.mem_filter.2 ⟨hx, by simpa using hs⟩)
        · simp at h
  | ex φ =>
    intro X p π φ' h
    unfold gxj at h
    split_ifs at h with hX
    · cases h; subst hX; exact .none
    · cases p <;> simp at h
  | ev a b φ =>
    intro X p π φ' h
    unfold gxj at h
    split_ifs at h with hX
    · cases h; subst hX; exact .none
    · cases p <;> simp at h
  | nx a b φ =>
    intro X p π φ' h
    unfold gxj at h
    split_ifs at h with hX
    · cases h; subst hX; exact .none
    · cases p <;> simp at h

end

/-! ## Rewriting (Figure 6) -/

/-- Peel a chain of unbounded nexts: `φ = ○ … ○ ψ` (`nxU`). -/
def peelNx : Fm B L D → ℕ × Fm B L D
  | .nx a b φ => if a = 0 ∧ b = none then ((peelNx φ).1 + 1, (peelNx φ).2) else (0, .nx a b φ)
  | φ => (0, φ)

theorem nxU_peelNx : ∀ φ : Fm B L D, nxU (peelNx φ).1 (peelNx φ).2 = φ := by
  intro φ
  induction φ with
  | nx a b φ ih =>
    unfold peelNx
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; simp only [nxU, ih]
    · rfl
  | _ => rfl

theorem sizeOf_peelNx : ∀ φ : Fm B L D, sizeOf (peelNx φ).2 ≤ sizeOf φ := by
  intro φ
  induction φ with
  | nx a b φ ih =>
    unfold peelNx
    split_ifs
    · simp only; simp only [Fm.nx.sizeOf_spec]; omega
    · exact le_rfl
  | _ => exact le_rfl

section
variable (S : Sig B L D)

/-- Rule `Ex^S`: extract a guard for the variable bound by the existential. -/
noncomputable def exGuard (c : Clause B L D) : Option (Clause B L D) :=
  (gx S.enum c.nloc true c.trig.guards c.trig.filter).map fun r => ⟨c.nloc + 1, ⟨r.1, r.2⟩, c.eff⟩

/-- `Γ ⊢ φ ↪^α 𝒞` (Figure 6): the candidate clause sets `𝒞` causing
    (`α = true`) or suppressing (`α = false`) `φ`.  For a suppressed
    conjunction, the left conjunct is suppressed if the right one is present,
    otherwise the right one. -/
noncomputable def rw : Bool → Fm B L D → Option (List (List (Clause B L D)))
  | true, .tt => some [[]]
  | true, .pred (.ev (.base e)) ts =>
    if S.cau e then some [[⟨0, Trigger.top, .cau (.base e) ts⟩]] else none
  | false, .pred (.ev (.base e)) ts =>
    if S.sup e then some [[⟨0, ⟨[[.pred (.ev (.base e)) ts]], .tt⟩, .sup (.base e) ts⟩]] else none
  | true, .pred (.lp p) ts =>
    if S.okC p ∧ ts.length = S.ar p then some [[⟨0, Trigger.top, .cau (.cau p) ts⟩]] else none
  | false, .pred (.lp p) ts =>
    if S.okS p ∧ ts.length = S.ar p then
      some [[⟨0, ⟨[[.pred (.lp p) ts]], .tt⟩, .cau (.sup p) ts⟩]] else none
  | pol, .neg φ => rw (!pol) φ
  | true, .conj φ ψ =>
    match rw true φ, rw true ψ with
    | some CS₁, some CS₂ => some (prodCS CS₁ CS₂)
    | _, _ => none
  | false, .conj φ ψ =>
    match (if ψ.present then rw false φ else none) with
    | some CS => some (CS.map (List.map (Clause.addFilter ψ)))
    | none =>
      if φ.present then (rw false ψ).map fun CS => CS.map (List.map (Clause.addFilter φ))
      else none
  | true, .ex φ => (rw true φ).map fun CS => CS.map (List.map (Clause.substCtx (instS 0 S.d₀)))
  | false, .ex φ => (rw false φ).map fun CS => CS.filterMap fun C => C.mapM (exGuard S)
  | true, .ev a b φ =>
    if a ≤ b ∧ 1 ≤ b then
      (rw true φ).map fun CS => CS.filterMap fun C =>
        if C ≠ [] ∧ ∀ c ∈ C, c.simple then some (C.map (Clause.mapCau (.later b))) else none
    else none
  | true, .nx a b φ =>
    if a = 0 then
      match b with
      | some b' =>
        if 1 ≤ b' then
          (rw true φ).map fun CS => CS.filterMap fun C =>
            if C ≠ [] ∧ ∀ c ∈ C, c.simple then some (C.map (Clause.mapCau (.next 1 true)))
            else none
        else none
      | none =>
        (rw true (peelNx φ).2).map fun CS => CS.filterMap fun C =>
          if ∀ c ∈ C, c.simple then
            some (C.map (Clause.mapCau (.next ((peelNx φ).1 + 1) false))) else none
    else none
  | _, _ => none
termination_by _ φ => sizeOf φ
decreasing_by
  all_goals first
    | (simp only [Fm.neg.sizeOf_spec]; omega)
    | (simp only [Fm.conj.sizeOf_spec]; omega)
    | (simp only [Fm.ex.sizeOf_spec]; omega)
    | (simp only [Fm.ev.sizeOf_spec]; omega)
    | (have := sizeOf_peelNx φ; simp only [Fm.nx.sizeOf_spec]; omega)

theorem forall₂_of_mapM {f : Clause B L D → Option (Clause B L D)} :
    ∀ {C C' : List (Clause B L D)}, C.mapM f = some C' → List.Forall₂ (fun c c' => f c = some c') C C'
  | [], C', h => by simp at h; subst h; exact .nil
  | c :: C, C', h => by
    rw [List.mapM_cons] at h
    rcases hc : f c with _ | c'
    · simp [hc] at h
    · rcases hC : C.mapM f with _ | C''
      · simp [hc, hC] at h
      · simp only [hc, hC] at h
        have h' : some (c' :: C'') = some C' := h
        cases h'; exact .cons hc (forall₂_of_mapM hC)

theorem exGuard_sound {c c' : Clause B L D} (h : exGuard S c = some c') : ExGuard S.enum c c' := by
  simp only [exGuard, Option.map_eq_some_iff] at h
  obtain ⟨⟨π, φ⟩, h₁, rfl⟩ := h
  exact ⟨rfl, rfl, gx_sound S.enum c.nloc _ _ _ _ _ h₁⟩

/-- **The rewriting function is sound**: its result is a derivation of the
    rewriting judgement. -/
theorem rw_sound : ∀ (pol : Bool) (φ : Fm B L D) (CS : List (List (Clause B L D))),
    rw S pol φ = some CS → Rw S pol φ CS
  | pol, φ, CS, h => by
    match pol, φ with
    | true, .tt => unfold rw at h; cases h; exact .tt
    | true, .pred (.ev (.base e)) ts =>
      unfold rw at h; split_ifs at h with he; cases h; exact .evC he
    | false, .pred (.ev (.base e)) ts =>
      unfold rw at h; split_ifs at h with he; cases h; exact .evS he
    | true, .pred (.lp p) ts =>
      unfold rw at h; split_ifs at h with he; cases h; exact .letC he.1 he.2
    | false, .pred (.lp p) ts =>
      unfold rw at h; split_ifs at h with he; cases h; exact .letS he.1 he.2
    | pol, .neg φ =>
      unfold rw at h
      exact .neg (rw_sound (!pol) φ CS (by cases pol <;> exact h))
    | true, .conj φ ψ =>
      unfold rw at h
      split at h
      · rename_i CS₁ CS₂ h₁ h₂
        cases h; exact .andC (rw_sound true φ _ h₁) (rw_sound true ψ _ h₂)
      · cases h
    | false, .conj φ ψ =>
      unfold rw at h
      split at h
      · rename_i CS₀ h₀
        cases h
        split_ifs at h₀ with hψ
        exact .andSL (rw_sound false φ _ h₀) hψ
      · split_ifs at h with hφ
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨CS₀, h₀, rfl⟩ := h
        exact .andSR (rw_sound false ψ _ h₀) hφ
    | true, .ex φ =>
      unfold rw at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨CS₀, h₀, rfl⟩ := h
      exact .exC (rw_sound true φ _ h₀)
    | false, .ex φ =>
      unfold rw at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨CS₀, h₀, rfl⟩ := h
      refine .exS (rw_sound false φ _ h₀) fun C' hC' => ?_
      obtain ⟨C, hC, hm⟩ := List.mem_filterMap.1 hC'
      exact ⟨C, hC, (forall₂_of_mapM hm).imp fun _ _ h => exGuard_sound S h⟩
    | true, .ev a b φ =>
      unfold rw at h
      split_ifs at h with hab
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨CS₀, h₀, rfl⟩ := h
      refine .futEv (rw_sound true φ _ h₀) hab.1 hab.2 fun C' hC' => ?_
      obtain ⟨C, hC, hm⟩ := List.mem_filterMap.1 hC'
      split_ifs at hm with hs
      cases hm
      exact ⟨C, hC, hs.1, hs.2, rfl⟩
    | true, .nx a b φ =>
      unfold rw at h
      split_ifs at h with ha
      subst ha
      split at h
      · rename_i b'
        split_ifs at h with hb
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨CS₀, h₀, rfl⟩ := h
        refine .futNx1 (rw_sound true φ _ h₀) hb fun C' hC' => ?_
        obtain ⟨C, hC, hm⟩ := List.mem_filterMap.1 hC'
        split_ifs at hm with hs
        cases hm
        exact ⟨C, hC, hs.1, hs.2, rfl⟩
      · simp only [Option.map_eq_some_iff] at h
        obtain ⟨CS₀, h₀, rfl⟩ := h
        have hR : Rw S true (nxU ((peelNx φ).1 + 1) (peelNx φ).2)
            (CS₀.filterMap fun C => if ∀ c ∈ C, c.simple then
              some (C.map (Clause.mapCau (.next ((peelNx φ).1 + 1) false))) else none) :=
          Rw.futNxU (rw_sound true (peelNx φ).2 _ h₀) (by omega) fun C' hC' => by
            obtain ⟨C, hC, hm⟩ := List.mem_filterMap.1 hC'
            split_ifs at hm with hs
            cases hm
            exact ⟨C, hC, hs, rfl⟩
        rwa [show nxU ((peelNx φ).1 + 1) (peelNx φ).2 = .nx 0 none φ by
          simp only [nxU, nxU_peelNx]] at hR
    | true, .pred (.ev (.cau _)) _ | true, .pred (.ev (.sup _)) _
    | false, .pred (.ev (.cau _)) _ | false, .pred (.ev (.sup _)) _
    | false, .tt | true, .eq _ _ | false, .eq _ _ | false, .ev _ _ _ | false, .nx _ _ _ =>
      unfold rw at h; cases h
termination_by _ φ => sizeOf φ
decreasing_by
  all_goals first
    | (simp only [Fm.neg.sizeOf_spec]; omega)
    | (simp only [Fm.conj.sizeOf_spec]; omega)
    | (simp only [Fm.ex.sizeOf_spec]; omega)
    | (simp only [Fm.ev.sizeOf_spec]; omega)
    | (have := sizeOf_peelNx φ; simp only [Fm.nx.sizeOf_spec]; omega)

end

/-! ## Monotonicity and presence -/

theorem GXJ.mono {m m' : Pr B L → Prop} (hm : ∀ p, m p → m' p) {X : List ℕ} {p : Bool}
    {φ φ' : Fm B L D} {π : Guards B L D} (h : GXJ m X p φ π φ') : GXJ m' X p φ π φ' := by
  induction h with
  | none => exact .none
  | vac => exact .vac
  | pred hp hx => exact .pred (hm _ hp) hx
  | eq hx => exact .eq hx
  | neg _ ih => exact .neg ih
  | andPos _ _ hX ih₁ ih₂ => exact .andPos ih₁ ih₂ hX
  | andNeg _ _ ih₁ ih₂ => exact .andNeg ih₁ ih₂

theorem Grd.mono {m m' : Pr B L → Prop} (hm : ∀ p, m p → m' p) {x : ℕ} {p : Bool}
    {φ : Fm B L D} (h : Grd m x p φ) : Grd m' x p φ := by
  induction h with
  | pred hp hx => exact .pred (hm _ hp) hx
  | eq => exact .eq
  | top => exact .top
  | neg _ ih => exact .neg ih
  | andL _ ih => exact .andL ih
  | andR _ ih => exact .andR ih
  | andNeg _ _ ih₁ ih₂ => exact .andNeg ih₁ ih₂

/-- Joint guard extraction shows every variable guarded. -/
theorem GXJ.grd {m : Pr B L → Prop} {X : List ℕ} {p : Bool} {φ φ' : Fm B L D}
    {π : Guards B L D} (h : GXJ m X p φ π φ') : ∀ x ∈ X, Grd m x p φ := by
  induction h with
  | none => intro x hx; cases hx
  | vac => intro x _; exact .top
  | pred hp hx => intro x h; exact .pred hp (hx x h)
  | eq hx => intro x h; rw [hx x h]; exact .eq
  | neg _ ih => intro x h; exact .neg (ih x h)
  | andPos _ _ hX ih₁ ih₂ =>
    intro x h
    rcases hX x h with h | h
    exacts [.andL (ih₁ x h), .andR (ih₂ x h)]
  | andNeg _ _ ih₁ ih₂ => intro x h; exact .andNeg (ih₁ x h) (ih₂ x h)

/-- A successful extraction from `(⊤, φ)` shows that `φ` is guarded. -/
theorem grd_of_gx {m : Pr B L → Prop} {x : ℕ} {p : Bool} {φ : Fm B L D}
    (h : (gx m x p [[]] φ).isSome) : Grd m x p φ := by
  obtain ⟨⟨π', φ'⟩, hr⟩ := Option.isSome_iff_exists.1 h
  rcases gx_iff.1 ⟨_, _, gx_sound m x φ p _ _ _ hr⟩ with hb | hg
  · obtain ⟨a, ha, -⟩ := hb [] (List.mem_singleton_self _); cases ha
  · exact hg

theorem Fm.present_disj (φ ψ : Fm B L D) : (Fm.disj φ ψ).present ↔ φ.present ∧ ψ.present :=
  Iff.rfl

theorem Guards.conjFm_present : ∀ κ : List (GAtom B L D), (Guards.conjFm κ).present
  | [] => trivial
  | a :: κ => by
    show (Fm.conj a.toFm (Guards.conjFm κ)).present
    exact ⟨by cases a <;> trivial, Guards.conjFm_present κ⟩

theorem Guards.toFm_present : ∀ π : Guards B L D, π.toFm.present
  | [] => trivial
  | κ :: π => (Fm.present_disj _ _).2 ⟨Guards.conjFm_present κ, Guards.toFm_present π⟩

theorem impFm_present (π : Guards B L D) {φ : Fm B L D} (h : φ.present) : (impFm π φ).present :=
  (Fm.present_disj _ _).2 ⟨Guards.toFm_present π, h⟩

theorem forall₂_mem_right' {α β : Type u} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => by cases hb
  | _, _, .cons hab h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨a, ha, h'⟩ := forall₂_mem_right' h b hb; exact ⟨a, List.mem_cons_of_mem _ ha, h'⟩

theorem GX.present {m : Pr B L → Prop} {x : ℕ} {p : Bool} {π π' : Guards B L D}
    {φ φ' : Fm B L D} (h : GX m x p π φ π' φ') (hφ : φ.present) : φ'.present := by
  induction h with
  | grd => exact hφ
  | vacPos => exact hφ
  | vacNeg => trivial
  | pred => trivial
  | eq => trivial
  | neg _ ih => exact ih hφ
  | andL _ ih => exact ⟨ih hφ.1, hφ.2⟩
  | andR _ ih => exact ⟨hφ.1, ih hφ.2⟩
  | andNeg _ _ ih₁ ih₂ =>
    exact ⟨impFm_present _ (ih₁ hφ.1), impFm_present _ (ih₂ hφ.2)⟩

theorem Clause.mapCau_trig (f : Ev B L → List (Term D) → Effect B L D) (c : Clause B L D) :
    (c.mapCau f).trig = c.trig := by
  unfold Clause.mapCau; split <;> rfl

/-- The rewriting produces clauses with present filters. -/
theorem Rw.present {S : Sig B L D} {pol : Bool} {φ : Fm B L D} {CS : List (List (Clause B L D))}
    (h : Rw S pol φ CS) : ∀ C ∈ CS, ∀ c ∈ C, c.trig.filter.present := by
  induction h with
  | tt => intro C hC c hc; simp at hC; subst hC; cases hc
  | evC | evS | letC | letS =>
    intro C hC c hc; simp at hC; subst hC; simp at hc; subst hc; trivial
  | neg _ ih => exact ih
  | andC _ _ ih₁ ih₂ =>
    intro C hC c hc
    obtain ⟨C₁, h₁, C₂, h₂, rfl⟩ : ∃ C₁ ∈ _, ∃ C₂ ∈ _, C₁ ++ C₂ = C := by
      simpa [prodCS] using hC
    rcases List.mem_append.1 hc with hc | hc
    exacts [ih₁ _ h₁ _ hc, ih₂ _ h₂ _ hc]
  | andSL _ hψ ih | andSR _ hψ ih =>
    intro C hC c hc
    obtain ⟨C₀, h₀, rfl⟩ := List.mem_map.1 hC
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact ⟨ih _ h₀ _ hc₀, Fm.present_subst _ _ hψ⟩
  | exC _ ih =>
    intro C hC c hc
    obtain ⟨C₀, h₀, rfl⟩ := List.mem_map.1 hC
    obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
    exact Fm.present_subst _ _ (ih _ h₀ _ hc₀)
  | exS _ hCS ih =>
    intro C' hC' c' hc'
    obtain ⟨C, hC, hF⟩ := hCS C' hC'
    obtain ⟨c, hc, hx⟩ := forall₂_mem_right' hF c' hc'
    exact hx.2.2.present (ih _ hC _ hc)
  | futEv _ _ _ hCS ih | futNx1 _ _ hCS ih =>
    intro C' hC' c' hc'
    obtain ⟨C, hC, -, -, rfl⟩ := hCS C' hC'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    rw [Clause.mapCau_trig]; exact ih _ hC _ hc
  | futNxU _ _ hCS ih =>
    intro C' hC' c' hc'
    obtain ⟨C, hC, -, rfl⟩ := hCS C' hC'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
    rw [Clause.mapCau_trig]; exact ih _ hC _ hc

end Generic

/-! ## `TypeLet`: the guards and realizations of the lets (Algorithm 3) -/

section TypeLet
variable {B D : Type}

/-- `TypeLet` for one let, with the predicates `m` enumerable: joint guard
    extraction from its value-producing operand for its guarded variables,
    giving its guards and the residual filter, provided guards for the negated
    left operand of a since can be extracted for the let's columns (the
    `remove` clause) and the terms of an aggregation only read guarded
    variables. -/
noncomputable def letGuards₂ (m : Pr B ℕ → Prop) (d : LetDef B ℕ D) :
    Option (Guards B ℕ D × Fm B ℕ D) :=
  match d.gop with
  | none => none
  | some φ =>
    if (∀ a b φl φr, d.body = .since a b φl φr →
          (gxj m (List.range d.arity) false φl).isSome) ∧
       (∀ k ω ts ys ψ, d.body = .agg k ω ts ys ψ → ∀ t ∈ ts, t.WF ∧ ∀ x ∈ t.supp, x ∈ d.gvars)
    then gxj m d.gvars true φ else none

/-- The guards of a let (`TypeLet`). -/
noncomputable def letGuards (m : Pr B ℕ → Prop) (d : LetDef B ℕ D) : Option (Guards B ℕ D) :=
  (letGuards₂ m d).map Prod.fst

variable (Γ : List (LetDef B ℕ D))

/-- The guards of the first `n` lets, each computed with the earlier lets
    enumerable (those with guards). -/
noncomputable def gdUpTo : ℕ → ℕ → Option (Guards B ℕ D)
  | 0 => fun _ => none
  | n + 1 => fun q => if q < n then gdUpTo n q else if q = n then
      (match Γ[n]? with
       | some d => letGuards (enumOf (gdUpTo n)) d
       | none => none)
      else none

/-- The guards of the lets. -/
noncomputable def gdOf (q : ℕ) : Option (Guards B ℕ D) := gdUpTo Γ (q + 1) q

theorem gdUpTo_ge : ∀ n q, n ≤ q → gdUpTo Γ n q = none
  | 0, _, _ => rfl
  | n + 1, q, h => by
    simp only [gdUpTo, show ¬ q < n by omega, show q ≠ n by omega, if_false]

theorem gdUpTo_stable : ∀ n q, q < n → gdUpTo Γ n q = gdOf Γ q
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, q, h => by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | rfl
    · simp only [gdUpTo, h', if_true]; exact gdUpTo_stable n q h'
    · rfl

theorem gdOf_eq (p : ℕ) :
    gdOf Γ p = match Γ[p]? with
      | some d => letGuards (enumOf (gdUpTo Γ p)) d
      | none => none := by
  simp [gdOf, gdUpTo]

theorem enum_gdUpTo (n : ℕ) : ∀ q, enumOf (gdUpTo Γ n) q → enumOf (gdOf Γ) q := by
  rintro (_ | q) h
  · trivial
  · simp only [enumOf] at h ⊢
    by_cases hq : q < n
    · rwa [← gdUpTo_stable Γ n q hq]
    · rw [gdUpTo_ge Γ n q (by omega)] at h; cases h

/-- The temporal lets (since, previous, aggregation) have guards. -/
def TemporalOK : Prop :=
  ∀ p (d : LetDef B ℕ D), Γ[p]? = some d →
    (∀ a b φl φr, d.body = .since a b φl φr → (gdOf Γ p).isSome) ∧
    (∀ a b φ, d.body = .prev a b φ → (gdOf Γ p).isSome) ∧
    (∀ k ω ts ys φ, d.body = .agg k ω ts ys φ → (gdOf Γ p).isSome)

theorem letGuards₂_spec {m : Pr B ℕ → Prop} {d : LetDef B ℕ D} {π : Guards B ℕ D}
    {φ' : Fm B ℕ D} (h : letGuards₂ m d = some (π, φ')) :
    (∃ φ, d.gop = some φ ∧ GXJ m d.gvars true φ π φ') ∧
    (∀ a b φl φr, d.body = .since a b φl φr → (gxj m (List.range d.arity) false φl).isSome) ∧
    (∀ k ω ts ys ψ, d.body = .agg k ω ts ys ψ → ∀ t ∈ ts, t.WF ∧ ∀ x ∈ t.supp, x ∈ d.gvars) := by
  unfold letGuards₂ at h
  split at h
  · cases h
  · rename_i φ hφ
    split_ifs at h with hc
    exact ⟨⟨φ, hφ, gxj_sound _ _ _ _ _ _ h⟩, hc.1, hc.2⟩

theorem gdOf_eq₂ (p : ℕ) :
    gdOf Γ p = match Γ[p]? with
      | some d => (letGuards₂ (enumOf (gdUpTo Γ p)) d).map Prod.fst
      | none => none := gdOf_eq Γ p

theorem letGuards_spec {p : ℕ} {d : LetDef B ℕ D} (hd : Γ[p]? = some d) {π : Guards B ℕ D}
    (h : gdOf Γ p = some π) :
    (∃ φ φ', d.gop = some φ ∧ GXJ (enumOf (gdOf Γ)) d.gvars true φ π φ') ∧
    (∀ a b φl φr, d.body = .since a b φl φr →
      Enum (enumOf (gdOf Γ)) (List.range d.arity) false φl) ∧
    (∀ k ω ts ys ψ, d.body = .agg k ω ts ys ψ → ∀ t ∈ ts, t.WF ∧ ∀ x ∈ t.supp, x ∈ d.gvars) := by
  rw [gdOf_eq₂, hd] at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨π', φ'⟩, h₂, rfl⟩ := h
  obtain ⟨⟨φ, hφ, hg⟩, hrem, hagg⟩ := letGuards₂_spec h₂
  refine ⟨⟨φ, φ', hφ, GXJ.mono (enum_gdUpTo Γ p) hg⟩, fun a b φl φr hb x hx => ?_, hagg⟩
  obtain ⟨⟨πr, φr'⟩, hr⟩ := Option.isSome_iff_exists.1 (hrem a b φl φr hb)
  exact Grd.mono (enum_gdUpTo Γ p) ((gxj_sound _ _ _ _ _ _ hr).grd x hx)

/-- **The guards computed by `TypeLet` satisfy `LetGuards`.** -/
theorem letGuards_ok (hT : TemporalOK Γ) : LetGuards Γ (gdOf Γ) where
  guards p d π hd h := (letGuards_spec Γ hd h).1
  removal p d a b φl φr hd hb hs := by
    obtain ⟨π, hπ⟩ := Option.isSome_iff_exists.1 hs
    exact (letGuards_spec Γ hd hπ).2.1 a b φl φr hb
  temporal p d hd := hT p d hd
  aggTerms p d k ω ts ys φ hd hb := by
    obtain ⟨π, hπ⟩ := Option.isSome_iff_exists.1 ((hT p d hd).2.2 k ω ts ys φ hb)
    exact (letGuards_spec Γ hd hπ).2.2 k ω ts ys φ hb

theorem gdOf_def {p : ℕ} (h : (gdOf Γ p).isSome) : (Γ[p]?).isSome := by
  rw [gdOf_eq] at h
  rcases hd : Γ[p]? with _ | d
  · rw [hd] at h; cases h
  · rfl

/-- The causation (`true`) or suppression (`false`) target of a let body. -/
def LBody.target (pol : Bool) (b : LBody B ℕ D) : Option (Fm B ℕ D) :=
  match pol with
  | true => b.cauTarget
  | false => b.supTarget

/-- The clauses of the items realizing the lets (`TypeLet`): for a guarded
    let, its guards and the residual filter of guard extraction (an unguarded
    let gets the `filter let` clause `if φ`); for a since, the `remove`
    clause `π_r if ¬φ_r'` extracted from its negated left operand; filters
    simplified (`Fm.simp`). -/
noncomputable def clsOf (p : ℕ) : LetCl B D :=
  match Γ[p]? with
  | none => ⟨Trigger.top, Trigger.top⟩
  | some d =>
    ⟨match letGuards₂ (enumOf (gdUpTo Γ p)) d with
      | some r => ⟨r.1, r.2.simp⟩
      | none => ⟨Guards.top, (d.gop.getD .tt).simp⟩,
     match d.body with
      | .since _ _ φl _ =>
        match gxj (enumOf (gdUpTo Γ p)) (List.range d.arity) false φl with
        | some r => ⟨r.1, (Fm.neg r.2).simp⟩
        | none => Trigger.top
      | _ => Trigger.top⟩

/-- **The clauses computed by `TypeLet` are those of guard extraction.** -/
theorem clsOf_ok (hT : TemporalOK Γ) : ClausesOK Γ (gdOf Γ) (clsOf Γ) := by
  intro p d hd
  have hg : gdOf Γ p = (letGuards₂ (enumOf (gdUpTo Γ p)) d).map Prod.fst := by
    rw [gdOf_eq₂, hd]
  refine ⟨fun φ hφ => ⟨fun π hπ => ?_, fun hn => ?_⟩, fun a b φl φr hb => ?_⟩
  · rw [hg] at hπ
    obtain ⟨⟨π', φ'⟩, h₂, rfl⟩ := Option.map_eq_some_iff.1 hπ
    obtain ⟨⟨φ₀, hφ₀, hx⟩, -, -⟩ := letGuards₂_spec h₂
    rw [hφ] at hφ₀; cases hφ₀
    exact ⟨φ', GXJ.mono (enum_gdUpTo Γ p) hx, by simp [clsOf, hd, h₂]⟩
  · rw [hg, Option.map_eq_none_iff] at hn
    simp [clsOf, hd, hn, hφ]
  · obtain ⟨π, hπ⟩ := Option.isSome_iff_exists.1 ((hT p d hd).1 a b φl φr hb)
    rw [hg] at hπ
    obtain ⟨⟨π', φ'⟩, h₂, -⟩ := Option.map_eq_some_iff.1 hπ
    obtain ⟨⟨πr, φr'⟩, hr⟩ := Option.isSome_iff_exists.1 ((letGuards₂_spec h₂).2.1 a b φl φr hb)
    exact ⟨πr, φr', GXJ.mono (enum_gdUpTo Γ p) (gxj_sound _ _ _ _ _ _ hr),
      by simp [clsOf, hd, hb, hr]⟩

variable (S₀ : Sig B ℕ D)

/-- The rewriting signature: the base events of `S₀`, the guarded lets
    enumerable. -/
noncomputable abbrev sig0 : Sig B ℕ D :=
  sigOf S₀ (enumOf (gdOf Γ)) (fun _ => False) (fun _ => False)

/-- The realization of let `n` (`TypeLet`): its causation (`pol = true`) or
    suppression target rewritten in the scope of the earlier lets realized by
    `R`; the first candidate clause set is chosen. -/
noncomputable def realOne (R : Real B ℕ D) (n : ℕ) (pol : Bool) : Option (List (Clause B ℕ D)) :=
  match Γ[n]? with
  | none => none
  | some d =>
    if (gdOf Γ n).isSome ∧ d.arity = S₀.ar n then
      match d.body.target pol with
      | none => none
      | some φ => (rw (R.scope (sig0 Γ S₀) (· < n)) pol φ).bind List.head?
    else none

/-- The realizations of the first `n` lets. -/
noncomputable def realUpTo : ℕ → Real B ℕ D
  | 0 => ⟨fun _ => none, fun _ => none⟩
  | n + 1 =>
    ⟨fun q => if q < n then (realUpTo n).cauCl q else
        if q = n then realOne Γ S₀ (realUpTo n) n true else none,
     fun q => if q < n then (realUpTo n).supCl q else
        if q = n then realOne Γ S₀ (realUpTo n) n false else none⟩

/-- The realization of the lets. -/
noncomputable def realOf : Real B ℕ D :=
  ⟨fun q => (realUpTo Γ S₀ (q + 1)).cauCl q, fun q => (realUpTo Γ S₀ (q + 1)).supCl q⟩

theorem realUpTo_stable : ∀ n q, q < n →
    (realUpTo Γ S₀ n).cauCl q = (realOf Γ S₀).cauCl q ∧
    (realUpTo Γ S₀ n).supCl q = (realOf Γ S₀).supCl q
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, q, h => by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | rfl
    · simp only [realUpTo, h', if_true]; exact realUpTo_stable n q h'
    · exact ⟨rfl, rfl⟩

theorem scope_realOf (p : ℕ) :
    (realOf Γ S₀).scope (sig0 Γ S₀) (· < p) = (realUpTo Γ S₀ p).scope (sig0 Γ S₀) (· < p) := by
  have h₁ : (fun q => q < p ∧ (realOf Γ S₀).cauCl q ≠ none) =
      fun q => q < p ∧ (realUpTo Γ S₀ p).cauCl q ≠ none := by
    funext q; apply propext
    exact ⟨fun ⟨hq, h⟩ => ⟨hq, by rwa [(realUpTo_stable Γ S₀ p q hq).1]⟩,
      fun ⟨hq, h⟩ => ⟨hq, by rwa [← (realUpTo_stable Γ S₀ p q hq).1]⟩⟩
  have h₂ : (fun q => q < p ∧ (realOf Γ S₀).supCl q ≠ none) =
      fun q => q < p ∧ (realUpTo Γ S₀ p).supCl q ≠ none := by
    funext q; apply propext
    exact ⟨fun ⟨hq, h⟩ => ⟨hq, by rwa [(realUpTo_stable Γ S₀ p q hq).2]⟩,
      fun ⟨hq, h⟩ => ⟨hq, by rwa [← (realUpTo_stable Γ S₀ p q hq).2]⟩⟩
  simp only [Real.scope, h₁, h₂]

theorem realOne_spec {p : ℕ} {pol : Bool} {C : List (Clause B ℕ D)}
    (h : realOne Γ S₀ (realUpTo Γ S₀ p) p pol = some C) :
    (gdOf Γ p).isSome ∧ ∃ d φ CS, Γ[p]? = some d ∧ d.arity = S₀.ar p ∧
      d.body.target pol = some φ ∧
      Rw ((realOf Γ S₀).scope (sig0 Γ S₀) (· < p)) pol φ CS ∧ C ∈ CS := by
  unfold realOne at h
  rcases hd : Γ[p]? with _ | d
  · rw [hd] at h; cases h
  · rw [hd] at h
    simp only at h
    split_ifs at h with hc
    split at h
    · cases h
    · rename_i φ hφ
      obtain ⟨CS, hCS, hC⟩ := Option.bind_eq_some_iff.1 h
      refine ⟨hc.1, d, φ, CS, rfl, hc.2, hφ, ?_, List.mem_of_mem_head? hC⟩
      rw [scope_realOf]; exact rw_sound _ _ _ _ hCS

theorem realOf_cau {p : ℕ} {C : List (Clause B ℕ D)} (h : (realOf Γ S₀).cauCl p = some C) :
    realOne Γ S₀ (realUpTo Γ S₀ p) p true = some C := by
  simpa [realOf, realUpTo] using h

theorem realOf_sup {p : ℕ} {C : List (Clause B ℕ D)} (h : (realOf Γ S₀).supCl p = some C) :
    realOne Γ S₀ (realUpTo Γ S₀ p) p false = some C := by
  simpa [realOf, realUpTo] using h

/-- **The realization computed by `TypeLet` is valid.** -/
theorem realOf_valid : (realOf Γ S₀).Valid (sig0 Γ S₀) (envOf Γ) (· < ·) where
  cau p C h := by
    obtain ⟨-, d, φ, CS, hd, har, hφ, hrw, hC⟩ := realOne_spec Γ S₀ (realOf_cau Γ S₀ h)
    exact ⟨d, φ, CS, hd, har, hφ, hrw, hC⟩
  sup p C h := by
    obtain ⟨-, d, φ, CS, hd, har, hφ, hrw, hC⟩ := realOne_spec Γ S₀ (realOf_sup Γ S₀ h)
    exact ⟨d, φ, CS, hd, har, hφ, hrw, hC⟩

theorem realOf_cauGuarded (p : ℕ) (h : (realOf Γ S₀).cauCl p ≠ none) : (gdOf Γ p).isSome := by
  obtain ⟨C, hC⟩ := Option.ne_none_iff_exists'.1 h
  exact (realOne_spec Γ S₀ (realOf_cau Γ S₀ hC)).1

theorem realOf_supGuarded (p : ℕ) (h : (realOf Γ S₀).supCl p ≠ none) : (gdOf Γ p).isSome := by
  obtain ⟨C, hC⟩ := Option.ne_none_iff_exists'.1 h
  exact (realOne_spec Γ S₀ (realOf_sup Γ S₀ hC)).1

end TypeLet

/-! ## `Generate`: the compilations of a policy -/

section Generate
variable {B D : Type} (S₀ : Sig B ℕ D)

/-- `Generate` (Algorithm 3): let-normalize `φ`, type its lets (`TypeLet`),
    and rewrite the enforced formula `χ` in the scope of all lets; one
    `Compilation` per candidate clause set. -/
noncomputable def compilations (φ : MF B D) : List (Σ Δ, Compilation S₀ φ Δ) :=
  if hT : TemporalOK (lnf φ).2 then
    match h : rw ((realOf (lnf φ).2 S₀).scope (sig0 (lnf φ).2 S₀) (fun _ => True)) true (lnf φ).1 with
    | none => []
    | some CS => CS.attach.map fun Δ =>
      ⟨Δ.1, { gd := gdOf (lnf φ).2
              R := realOf (lnf φ).2 S₀
              CS := CS
              guards := letGuards_ok _ hT
              guardsDef := fun _ hp => gdOf_def _ hp
              cauGuarded := realOf_cauGuarded _ S₀
              supGuarded := realOf_supGuarded _ S₀
              valid := realOf_valid _ S₀
              rewrite := rw_sound _ _ _ _ h
              choice := Δ.2 }⟩
  else []

theorem mem_compilations {φ : MF B D} {x : Σ Δ, Compilation S₀ φ Δ}
    (h : x ∈ compilations S₀ φ) : TemporalOK (lnf φ).2 ∧ x.2.gd = gdOf (lnf φ).2 := by
  unfold compilations at h
  split_ifs at h with hT
  · split at h
    · cases h
    · obtain ⟨Δ, -, rfl⟩ := List.mem_map.1 h
      exact ⟨hT, rfl⟩
  · cases h

end Generate

/-! ## `Compile`: the EF programs (Algorithm 4) -/

section CompileProg
variable {B D : Type}

/-- The gated realization clauses of the lets `0 … n-1`. -/
def realClauses (R : Real B ℕ D) (ar : ℕ → ℕ) (n : ℕ) : List (Clause B ℕ D) :=
  (List.range n).flatMap fun p =>
    ((R.cauCl p).getD []).map (gate (.cau p) (ar p)) ++ ((R.supCl p).getD []).map (gate (.sup p) (ar p))

theorem mem_realClauses {R : Real B ℕ D} {ar : ℕ → ℕ} {n : ℕ} {c : Clause B ℕ D} :
    c ∈ realClauses R ar n ↔ ∃ p < n,
      (∃ C, R.cauCl p = some C ∧ ∃ c₀ ∈ C, c = gate (.cau p) (ar p) c₀) ∨
      (∃ C, R.supCl p = some C ∧ ∃ c₀ ∈ C, c = gate (.sup p) (ar p) c₀) := by
  have key : ∀ (o : Option (List (Clause B ℕ D))) (g : Clause B ℕ D → Clause B ℕ D),
      c ∈ (o.getD []).map g ↔ ∃ C, o = some C ∧ ∃ c₀ ∈ C, c = g c₀ := by
    intro o g
    cases o with
    | none => simp
    | some C =>
      simp only [Option.getD_some, List.mem_map, Option.some.injEq, exists_eq_left']
      exact ⟨fun ⟨c₀, h₁, h₂⟩ => ⟨c₀, h₁, h₂.symm⟩, fun ⟨c₀, h₁, h₂⟩ => ⟨c₀, h₁, h₂.symm⟩⟩
  simp only [realClauses, List.mem_flatMap, List.mem_range, List.mem_append, key]

/-- **`Compile(Γ, R, ≺)`** (Algorithm 4): for every compilation of the policy,
    the program whose rules are the candidate clause set and the gated
    realization clauses, sectioned along a topological order of the SCCs of
    the EDG.  `v₀` is the default valuation; `stab` are the user's stability
    labels (`sfun`), trusted to be sound (`hstab`). -/
noncomputable def compile (Φ : Policy B D) (S₀ : Sig B ℕ D) (v₀ : ℕ → D) (stab : Term D → Prop)
    (hstab : ∃ Stab : Set D → Set D, StabOp Stab ∧ ∀ t, stab t → t.stableIn Stab) :
    List (Compiled Φ) :=
  (compilations S₀ Φ.φ).attach.map fun ⟨⟨Δ, comp⟩, hx⟩ =>
    let rules := Δ ++ realClauses comp.R S₀.ar Φ.Γ.length
    { S₀ := S₀
      C := Δ
      comp := comp
      rules := rules
      v₀ := v₀
      hasC := fun c hc => List.mem_append_left _ hc
      hasR := fun c hc => by
        refine List.mem_append_right _ (mem_realClauses.2 ?_)
        have hlt : ∀ p, (comp.gd p).isSome → p < Φ.Γ.length := fun p hp => by
          have := comp.guardsDef p hp
          by_contra hge
          simp only [Policy.Γ] at hge
          rw [List.getElem?_eq_none (by omega)] at this; cases this
        rcases hc with ⟨p, C, hC, c₀, hc₀, rfl⟩ | ⟨p, C, hC, c₀, hc₀, rfl⟩
        · exact ⟨p, hlt p (comp.cauGuarded p (by rw [hC]; simp)), Or.inl ⟨C, hC, c₀, hc₀, rfl⟩⟩
        · exact ⟨p, hlt p (comp.supGuarded p (by rw [hC]; simp)), Or.inr ⟨C, hC, c₀, hc₀, rfl⟩⟩
      only := fun c hc => by
        rcases List.mem_append.1 hc with hc | hc
        · exact Or.inl hc
        · obtain ⟨p, -, h⟩ := mem_realClauses.1 hc
          rcases h with ⟨C, hC, c₀, hc₀, rfl⟩ | ⟨C, hC, c₀, hc₀, rfl⟩
          · exact Or.inr (Or.inl ⟨p, C, hC, c₀, hc₀, rfl⟩)
          · exact Or.inr (Or.inr ⟨p, C, hC, c₀, hc₀, rfl⟩)
      present := fun c hc => by
        rcases List.mem_append.1 hc with hc | hc
        · exact comp.rewrite.present Δ comp.choice c hc
        · obtain ⟨p, -, h⟩ := mem_realClauses.1 hc
          rcases h with ⟨C, hC, c₀, hc₀, rfl⟩ | ⟨C, hC, c₀, hc₀, rfl⟩
          · obtain ⟨d, φ, CS, -, -, -, hrw, hCS⟩ := comp.valid.cau p C hC
            exact hrw.present C hCS c₀ hc₀
          · obtain ⟨d, φ, CS, -, -, -, hrw, hCS⟩ := comp.valid.sup p C hC
            exact hrw.present C hCS c₀ hc₀
      secs := sccOrder (ldOf Φ.Γ) rules
      order := sccOrder_spec _ _
      stab := stab
      stab_sound := hstab
      cls := clsOf Φ.Γ
      clsOK := by
        obtain ⟨hT, hgd⟩ := mem_compilations S₀ hx
        simp only at hgd
        rw [hgd]; exact clsOf_ok _ hT }

/-- Every compilation yields a program of `compile`, with its clause set. -/
theorem mem_compile {Φ : Policy B D} {S₀ : Sig B ℕ D} {v₀ : ℕ → D} {stab : Term D → Prop}
    {hstab : ∃ Stab : Set D → Set D, StabOp Stab ∧ ∀ t, stab t → t.stableIn Stab}
    {x : Σ Δ, Compilation S₀ Φ.φ Δ} (hx : x ∈ compilations S₀ Φ.φ) :
    ∃ P ∈ compile Φ S₀ v₀ stab hstab, P.C = x.1 := by
  obtain ⟨Δ, comp⟩ := x
  exact ⟨_, List.mem_map.2 ⟨⟨⟨Δ, comp⟩, hx⟩, List.mem_attach _ _, rfl⟩, rfl⟩

/-- The programs returned by `compile` use the given default valuation. -/
theorem compile_v₀ {Φ : Policy B D} {S₀ : Sig B ℕ D} {v₀ : ℕ → D} {stab : Term D → Prop}
    {hstab : ∃ Stab : Set D → Set D, StabOp Stab ∧ ∀ t, stab t → t.stableIn Stab}
    {P : Compiled Φ} (hP : P ∈ compile Φ S₀ v₀ stab hstab) : P.v₀ = v₀ := by
  obtain ⟨⟨⟨Δ, comp⟩, hx⟩, -, rfl⟩ := List.mem_map.1 hP
  rfl

/-- Every program returned by `compile` whose two checks pass (the conflict
    check on the EDG, with a sound SMT solver `S`, and the data-flow check on
    the DFG) is a sound enforcer of `□φ`. -/
theorem compile_sound {Φ : Policy B D} {S₀ : Sig B ℕ D} {v₀ : ℕ → D} {stab : Term D → Prop}
    {hstab : ∃ Stab : Set D → Set D, StabOp Stab ∧ ∀ t, stab t → t.stableIn Stab}
    {P : Compiled Φ} (hP : P ∈ compile Φ S₀ v₀ stab hstab)
    {S : SMT PEmpty (QSym B ℕ) D} (h : P.Checks S) :
    SoundEnforcer Φ.φ v₀ (enforce P h) := by
  rw [← compile_v₀ hP]
  exact compiled_sound P h

/-- **EnfFlash**: compile the policy (`compile`), keep the first program whose
    two checks pass, and return the enforcer running it (Algorithm 1); none if
    no program passes the checks. -/
noncomputable def enfflash (Φ : Policy B D) (S₀ : Sig B ℕ D) (v₀ : ℕ → D) (stab : Term D → Prop)
    (hstab : ∃ Stab : Set D → Set D, StabOp Stab ∧ ∀ t, stab t → t.stableIn Stab)
    (S : SMT PEmpty (QSym B ℕ) D) : Option (InputTrace B D → Tr B ℕ D) :=
  match h : (compile Φ S₀ v₀ stab hstab).find? (fun P : Compiled Φ => decide (P.Checks S)) with
  | none => none
  | some P =>
    some (enforce P (of_decide_eq_true (List.find?_some (p := fun P : Compiled Φ => decide (P.Checks S)) h)))

/-- **End-to-end correctness of EnfFlash** (paper, Theorem 4.5: *Compilation
    correctness*).  If EnfFlash, run on the policy `□φ` (with the signature
    `S₀`, the default valuation `v₀`, the stability labels `stab`, and a sound
    SMT solver `S`), returns an enforcer `E`, then `E` is a sound enforcer of
    `□φ`: on every valid input trace, its output satisfies `□φ`. -/
theorem enforcement_correct (Φ : Policy B D) (S₀ : Sig B ℕ D) (v₀ : ℕ → D)
    (stab : Term D → Prop)
    (hstab : ∃ Stab : Set D → Set D, StabOp Stab ∧ ∀ t, stab t → t.stableIn Stab)
    (S : SMT PEmpty (QSym B ℕ) D) {E : InputTrace B D → Tr B ℕ D}
    (hE : enfflash Φ S₀ v₀ stab hstab S = some E) :
    SoundEnforcer Φ.φ v₀ E := by
  unfold enfflash at hE
  split at hE
  · cases hE
  · rename_i P hP
    cases hE
    exact compile_sound (List.mem_of_find?_eq_some hP) _

end CompileProg

end Enfflash
