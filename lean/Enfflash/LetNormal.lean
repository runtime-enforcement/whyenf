/-
  Enfflash formalization — let-normalization (paper, Section 4.1).

  MFOTL formulas (`MF`, defined in `MFOTL.lean`, with arbitrarily nested past
  and future operators) are translated to let-normal form (`Fm`): every past subformula
  (`●_I φ`, `φ S_I ψ`, hence `⧫_I φ = ⊤ S_I φ`) is bound to a fresh
  let-predicate over its free variables, whose body is again in let-normal
  form, so that past operators only occur at the top of let bodies.

  Source-level let bindings `let p(x̄) = φ in ψ` become present lets, and
  every future-free existential subformula is bound to a let as well (as the
  compiler's `Exists` lets), so that quantifiers in the enforced formula only
  range over subformulas with future operators.

  `norm_correct`: under the let definitions produced, the normalized formula
  is equivalent to the original one at every time-point, under every
  valuation.  `norm_ordered`: the body of every let only refers to earlier
  lets (so the realization order `(· < ·)` is well-founded).  `norm_shape`:
  the result is in let-normal form.  `norm_presentOps`: for policies whose
  past operators and let bodies are future-free, all let operands are present
  formulas (as required by the tables).
-/
import Enfflash.MFOTL

namespace Enfflash

universe u

/-! ## Free variables -/

section
variable {B L D : Type u}

/-- Free variables (function terms contribute their support). -/
def Fm.fv : Fm B L D → List ℕ
  | .tt => []
  | .pred _ ts => ts.flatMap Term.supp
  | .eq t u => t.supp ++ u.supp
  | .neg φ | .ev _ _ φ | .nx _ _ φ => φ.fv
  | .conj φ ψ => φ.fv ++ ψ.fv
  | .ex φ => φ.fv.filterMap fun n => match n with | 0 => none | n + 1 => some n

/-- All function terms read only their support. -/
def Fm.WF : Fm B L D → Prop
  | .tt => True
  | .pred _ ts => ∀ t ∈ ts, t.WF
  | .eq t u => t.WF ∧ u.WF
  | .neg φ | .ex φ | .ev _ _ φ | .nx _ _ φ => φ.WF
  | .conj φ ψ => φ.WF ∧ ψ.WF

theorem Term.WF_subst {t : Term D} (ht : t.WF) {s : ℕ → Term D} (hs : ∀ n, (s n).WF) :
    (t.subst s).WF := by
  cases t with
  | var n => exact hs n
  | const => trivial
  | fn f xs =>
    intro w w' h
    apply ht
    intro n hn
    exact Term.eval_congr _ (hs n) w w' fun m hm => h m (List.mem_flatMap.2 ⟨n, hn, hm⟩)

theorem upS_WF {s : ℕ → Term D} (hs : ∀ n, (s n).WF) : ∀ n, (upS s n).WF
  | 0 => trivial
  | n + 1 => Term.WF_subst (hs n) fun _ => trivial

theorem Fm.WF_subst {φ : Fm B L D} (hφ : φ.WF) :
    ∀ {s : ℕ → Term D}, (∀ n, (s n).WF) → (φ.subst s).WF := by
  induction φ with
  | tt => intros; trivial
  | pred p ts =>
    intro s hs t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact Term.WF_subst (hφ t' ht') hs
  | eq t u => intro s hs; exact ⟨Term.WF_subst hφ.1 hs, Term.WF_subst hφ.2 hs⟩
  | neg φ ih => intro s hs; exact ih hφ hs
  | conj φ ψ ih₁ ih₂ => intro s hs; exact ⟨ih₁ hφ.1 hs, ih₂ hφ.2 hs⟩
  | ex φ ih => intro s hs; exact ih hφ (upS_WF hs)
  | ev a b φ ih => intro s hs; exact ih hφ hs
  | nx a b φ ih => intro s hs; exact ih hφ hs

theorem map_eval_congr {ts : List (Term D)} (hts : ∀ t ∈ ts, t.WF) {v v' : ℕ → D}
    (h : ∀ n ∈ ts.flatMap Term.supp, v n = v' n) :
    ts.map (Term.eval v) = ts.map (Term.eval v') :=
  List.map_congr_left fun t ht =>
    Term.eval_congr t (hts t ht) v v' fun n hn => h n (List.mem_flatMap.2 ⟨t, ht, hn⟩)

/-- Satisfaction only depends on the free variables. -/
theorem Tr.sat_fv (σ : Tr B L D) {φ : Fm B L D} (hφ : φ.WF) :
    ∀ i (v v' : ℕ → D), (∀ n ∈ φ.fv, v n = v' n) → (σ.sat i v φ ↔ σ.sat i v' φ) := by
  induction φ with
  | tt => intros; rfl
  | pred p ts => intro i v v' h; simp only [Tr.sat]; rw [map_eval_congr hφ h]
  | eq t u =>
    intro i v v' h
    simp only [Tr.sat]
    rw [Term.eval_congr t hφ.1 v v' fun n hn => h n (List.mem_append_left _ hn),
      Term.eval_congr u hφ.2 v v' fun n hn => h n (List.mem_append_right _ hn)]
  | neg φ ih => intro i v v' h; simp only [Tr.sat]; rw [ih hφ i v v' h]
  | conj φ ψ ih₁ ih₂ =>
    intro i v v' h
    simp only [Tr.sat]
    rw [ih₁ hφ.1 i v v' fun n hn => h n (List.mem_append_left _ hn),
      ih₂ hφ.2 i v v' fun n hn => h n (List.mem_append_right _ hn)]
  | ex φ ih =>
    intro i v v' h
    simp only [Tr.sat]
    refine exists_congr fun d => ih hφ i _ _ fun n hn => ?_
    cases n with
    | zero => rfl
    | succ n => exact h n (List.mem_filterMap.2 ⟨n + 1, hn, rfl⟩)
  | ev a b φ ih =>
    intro i v v' h
    simp only [Tr.sat]
    exact exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => ih hφ j v v' h
  | nx a b φ ih => intro i v v' h; simp only [Tr.sat]; rw [ih hφ _ v v' h]

/-- Let predicates referenced by a formula. -/
def Fm.lets : Fm B L D → List L
  | .pred (.lp p) _ => [p]
  | .tt | .pred _ _ | .eq _ _ => []
  | .neg φ | .ex φ | .ev _ _ φ | .nx _ _ φ => φ.lets
  | .conj φ ψ => φ.lets ++ ψ.lets

theorem Fm.lets_subst (φ : Fm B L D) : ∀ s : ℕ → Term D, (φ.subst s).lets = φ.lets := by
  induction φ with
  | pred p ts => intro s; cases p <;> rfl
  | tt | eq => intro; rfl
  | neg φ ih | ex φ ih | ev _ _ φ ih | nx _ _ φ ih => intro s; exact ih _
  | conj φ ψ ih₁ ih₂ => intro s; simp [Fm.subst, Fm.lets, ih₁, ih₂]

end

/-! ## Normalization -/

section
variable {B D : Type}

/-- Decidable presence. -/
def Fm.isPresent {L : Type} : Fm B L D → Bool
  | .tt | .pred _ _ | .eq _ _ => true
  | .neg φ | .ex φ => φ.isPresent
  | .conj φ ψ => φ.isPresent && ψ.isPresent
  | .ev _ _ _ | .nx _ _ _ => false

theorem Fm.isPresent_iff {L : Type} (φ : Fm B L D) : φ.isPresent = true ↔ φ.present := by
  induction φ with
  | conj φ ψ ih₁ ih₂ => simp [isPresent, present, ih₁, ih₂]
  | neg φ ih | ex φ ih => exact ih
  | _ => simp [isPresent, present]

/-- Rename the variables `xs` to `0, …, |xs|-1`. -/
def ren (xs : List ℕ) : ℕ → Term D := fun n => .var (xs.idxOf n)

/-- The atom `p(xs)`. -/
def letAtom (p : ℕ) (xs : List ℕ) : Fm B ℕ D := .pred (.lp p) (xs.map .var)

/-- Let-normalization.  Lets are numbered in order of creation; `Γ` is the
    list of lets created so far and `U` maps the enclosing source lets to
    their let numbers. -/
def norm : MF B D → List ℕ → List (LetDef B ℕ D) → Fm B ℕ D × List (LetDef B ℕ D)
  | .tt, _, Γ => (.tt, Γ)
  | .pred e ts, _, Γ => (.pred (.ev (.base e)) ts, Γ)
  | .upred k ts, U, Γ => (.pred (.lp (U.getD k 0)) ts, Γ)
  | .eq t u, _, Γ => (.eq t u, Γ)
  | .neg φ, U, Γ => let r := norm φ U Γ; (.neg r.1, r.2)
  | .conj φ ψ, U, Γ => let r₁ := norm φ U Γ; let r₂ := norm ψ U r₁.2; (.conj r₁.1 r₂.1, r₂.2)
  | .ex φ, U, Γ =>
    let r := norm φ U Γ
    if r.1.isPresent then
      let xs := (Fm.ex r.1).fv
      (letAtom r.2.length xs, r.2 ++ [⟨xs.length, .now (.ex (r.1.subst (upS (ren xs))))⟩])
    else (.ex r.1, r.2)
  | .nx a b φ, U, Γ => let r := norm φ U Γ; (.nx a b r.1, r.2)
  | .ev a b φ, U, Γ => let r := norm φ U Γ; (.ev a b r.1, r.2)
  | .prev a b φ, U, Γ =>
    let r := norm φ U Γ
    let xs := r.1.fv
    (letAtom r.2.length xs, r.2 ++ [⟨xs.length, .prev a b (r.1.subst (ren xs))⟩])
  | .since a b φ ψ, U, Γ =>
    let r₁ := norm φ U Γ
    let r₂ := norm ψ U r₁.2
    let xs := r₁.1.fv ++ r₂.1.fv
    (letAtom r₂.2.length xs,
      r₂.2 ++ [⟨xs.length, .since a b (r₁.1.subst (ren xs)) (r₂.1.subst (ren xs))⟩])
  | .letin ar body rest, U, Γ =>
    let r₁ := norm body U Γ
    norm rest (r₁.2.length :: U) (r₁.2 ++ [⟨ar, .now r₁.1⟩])
  | .agg k ω ts ys φ, U, Γ =>
    let r := norm φ U Γ
    let xs := (r.1.fv ++ ts.flatMap Term.supp).filterMap (shiftOut k) ++ ys
    (letAtom r.2.length xs, r.2 ++ [⟨xs.length, .agg k ω (ts.map (Term.subst (upSn k (ren xs))))
      (ys.map xs.idxOf) (r.1.subst (upSn k (ren xs)))⟩])

/-- The let environment of a list of lets. -/
def envOf (Γ : List (LetDef B ℕ D)) : ℕ → Option (LetDef B ℕ D) := fun p => Γ[p]?

theorem letSem_prefix {Γ Γ' : List (LetDef B ℕ D)} (h : Γ <+: Γ') {σ : Tr B ℕ D}
    {v₀ : ℕ → D} (hs : LetSem (envOf Γ') σ v₀) : LetSem (envOf Γ) σ v₀ := by
  intro p d hd
  apply hs p d
  obtain ⟨t, rfl⟩ := h
  simp only [envOf] at hd ⊢
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hd).1]; exact hd

theorem vapp_ren (xs : List ℕ) (v v₀ : ℕ → D) :
    ∀ n ∈ xs, (fun m => (ren xs m).eval (vapp (xs.map v) v₀)) n = v n := by
  intro n hn
  have hlt := List.idxOf_lt_length_of_mem hn
  simp only [ren, Term.eval]
  rw [vapp_lt _ _ _ (by simpa using hlt), List.getElem_map, List.getElem_idxOf hlt]

theorem letAtom_sat {σ : Tr B ℕ D} {i : ℕ} {v : ℕ → D} {p : ℕ} {xs : List ℕ} :
    σ.sat i v (letAtom p xs) ↔ σ.lv i p (xs.map v) := by
  simp [letAtom, Tr.sat, Tr.prIn, List.map_map, Function.comp_def, Term.eval]

theorem envOf_last (Γ : List (LetDef B ℕ D)) (d : LetDef B ℕ D) :
    envOf (Γ ++ [d]) Γ.length = some d := by
  simp [envOf]

theorem letAtom_WF (p : ℕ) (xs : List ℕ) : (letAtom (B := B) (D := D) p xs).WF := by
  intro t ht; obtain ⟨n, -, rfl⟩ := List.mem_map.1 ht; trivial

theorem letAtom_fv (p : ℕ) (xs : List ℕ) : (letAtom (B := B) (D := D) p xs).fv = xs := by
  simp only [letAtom, Fm.fv]
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Term.supp, ih]

theorem filterMap_pred_mono {l l' : List ℕ} (h : ∀ n ∈ l, n ∈ l') :
    ∀ n ∈ l.filterMap (fun n => match n with | 0 => none | n + 1 => some n),
      n ∈ l'.filterMap (fun n => match n with | 0 => none | n + 1 => some n) := by
  intro n hn
  obtain ⟨m, hm, hmn⟩ := List.mem_filterMap.1 hn
  exact List.mem_filterMap.2 ⟨m, h m hm, hmn⟩

theorem norm_prefix (φ : MF B D) : ∀ U (Γ : List (LetDef B ℕ D)), Γ <+: (norm φ U Γ).2 := by
  induction φ with
  | tt | eq | pred | upred => intro U Γ; exact List.prefix_refl _
  | neg φ ih | nx _ _ φ ih | ev _ _ φ ih => intro U Γ; exact ih U Γ
  | ex φ ih =>
    intro U Γ; simp only [norm]; split
    · exact (ih U Γ).trans (List.prefix_append _ _)
    · exact ih U Γ
  | conj φ ψ ih₁ ih₂ => intro U Γ; exact (ih₁ U Γ).trans (ih₂ _ _)
  | prev a b φ ih => intro U Γ; exact (ih U Γ).trans (List.prefix_append _ _)
  | agg k ω ts ys φ ih => intro U Γ; exact (ih U Γ).trans (List.prefix_append _ _)
  | since a b φ ψ ih₁ ih₂ =>
    intro U Γ; exact ((ih₁ U Γ).trans (ih₂ _ _)).trans (List.prefix_append _ _)
  | letin ar body rest ih₁ ih₂ =>
    intro U Γ; exact ((ih₁ U Γ).trans (List.prefix_append _ _)).trans (ih₂ _ _)

/-- The source lets are interpreted by the lets they were mapped to. -/
def UEnvOK (σ : Tr B ℕ D) (U : List ℕ) (ρ : List (ℕ → List D → Prop)) (ars : List ℕ) : Prop :=
  ∀ k ar, ars[k]? = some ar → ∃ P, ρ[k]? = some P ∧
    ∀ i (as : List D), as.length = ar → (P i as ↔ σ.lv i (U.getD k 0) as)

/-- **Correctness of let-normalization.** -/
theorem norm_correct (φ : MF B D) : ∀ ars, φ.WF ars → ∀ U (Γ : List (LetDef B ℕ D)),
    (norm φ U Γ).1.WF ∧ (∀ n ∈ (norm φ U Γ).1.fv, n ∈ φ.fv) ∧
      ∀ (σ : Tr B ℕ D) (v₀ : ℕ → D) ρ, LetSem (envOf (norm φ U Γ).2) σ v₀ →
        UEnvOK σ U ρ ars → ∀ i v, (σ.sat i v (norm φ U Γ).1 ↔ φ.sat σ ρ i v) := by
  induction φ with
  | tt => intro ars _ U Γ; exact ⟨trivial, by simp [norm, Fm.fv], fun _ _ _ _ _ _ _ => by simp [Tr.sat, MF.sat, norm]⟩
  | pred e ts =>
    intro ars hφ U Γ
    exact ⟨hφ, fun n hn => hn, fun _ _ _ _ _ _ _ => by simp [Tr.sat, Tr.prIn, MF.sat, norm]⟩
  | upred k ts =>
    intro ars hφ U Γ
    refine ⟨hφ.2, fun n hn => hn, fun σ v₀ ρ _ hU i v => ?_⟩
    obtain ⟨P, hP, hPi⟩ := hU k _ hφ.1
    simp only [norm, Tr.sat, Tr.prIn, MF.sat, hP, Option.some.injEq, exists_eq_left']
    exact (hPi i _ (by simp)).symm
  | eq t u => intro ars hφ U Γ; exact ⟨hφ, fun n hn => hn, fun _ _ _ _ _ _ _ => by simp [Tr.sat, MF.sat, norm]⟩
  | neg φ ih =>
    intro ars hφ U Γ
    obtain ⟨h1, h2, h3⟩ := ih ars hφ U Γ
    exact ⟨h1, h2, fun σ v₀ ρ hs hU i v => by simp only [norm, Tr.sat, MF.sat]; rw [h3 σ v₀ ρ hs hU]⟩
  | nx a b φ ih =>
    intro ars hφ U Γ
    obtain ⟨h1, h2, h3⟩ := ih ars hφ U Γ
    exact ⟨h1, h2, fun σ v₀ ρ hs hU i v => by simp only [norm, Tr.sat, MF.sat]; rw [h3 σ v₀ ρ hs hU]⟩
  | ev a b φ ih =>
    intro ars hφ U Γ
    obtain ⟨h1, h2, h3⟩ := ih ars hφ U Γ
    exact ⟨h1, h2, fun σ v₀ ρ hs hU i v => by
      simp only [norm, Tr.sat, MF.sat]
      exact exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ =>
        and_congr_right fun _ => h3 σ v₀ ρ hs hU j v⟩
  | conj φ ψ ih₁ ih₂ =>
    intro ars hφ U Γ
    obtain ⟨h1, h2, h3⟩ := ih₁ ars hφ.1 U Γ
    obtain ⟨g1, g2, g3⟩ := ih₂ ars hφ.2 U (norm φ U Γ).2
    refine ⟨⟨h1, g1⟩, fun n hn => ?_, fun σ v₀ ρ hs hU i v => ?_⟩
    · rcases List.mem_append.1 hn with hn | hn
      exacts [List.mem_append_left _ (h2 n hn), List.mem_append_right _ (g2 n hn)]
    · simp only [norm, Tr.sat, MF.sat]
      rw [h3 σ v₀ ρ (letSem_prefix (norm_prefix ψ _ _) hs) hU, g3 σ v₀ ρ hs hU]
  | ex φ ih =>
    intro ars hφ U Γ
    obtain ⟨h1, h2, h3⟩ := ih ars hφ U Γ
    simp only [norm]
    split
    · refine ⟨letAtom_WF _ _, ?_, fun σ v₀ ρ hs hU i v => ?_⟩
      · rw [letAtom_fv]; exact filterMap_pred_mono h2
      · rw [letAtom_sat]
        set χ := (norm φ U Γ).1
        set xs := (Fm.ex χ).fv
        have hiff := hs _ _ (envOf_last _ _) i (xs.map v) (by simp only [List.length_map])
        rw [hiff]
        simp only [LBody.sem, Tr.sat, MF.sat]
        refine exists_congr fun d => ?_
        rw [Tr.sat_subst, eval_upS, Tr.sat_fv σ h1 _ _ (vcons d v) fun n hn => ?_,
          h3 σ v₀ ρ (letSem_prefix (List.prefix_append _ _) hs) hU]
        cases n with
        | zero => rfl
        | succ n => exact vapp_ren xs v v₀ n (List.mem_filterMap.2 ⟨n + 1, hn, rfl⟩)
    · exact ⟨h1, filterMap_pred_mono h2, fun σ v₀ ρ hs hU i v => by
        simp only [Tr.sat, MF.sat]; exact exists_congr fun d => h3 σ v₀ ρ hs hU i _⟩
  | prev a b φ ih =>
    intro ars hφ U Γ
    obtain ⟨h1, h2, h3⟩ := ih ars hφ U Γ
    refine ⟨letAtom_WF _ _, by rw [norm, letAtom_fv]; exact h2, fun σ v₀ ρ hs hU i v => ?_⟩
    simp only [norm]
    rw [letAtom_sat]
    set χ := (norm φ U Γ).1
    set xs := χ.fv
    have hiff := hs _ _ (envOf_last _ _) i (xs.map v) (by simp only [List.length_map]; rfl)
    rw [hiff]
    simp only [LBody.sem, MF.sat]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [Tr.sat_subst, Tr.sat_fv σ h1 _ _ v (vapp_ren xs v v₀),
      h3 σ v₀ ρ (letSem_prefix (List.prefix_append _ _) hs) hU]
  | since a b φ ψ ih₁ ih₂ =>
    intro ars hφ U Γ
    obtain ⟨h1, h2, h3⟩ := ih₁ ars hφ.1 U Γ
    obtain ⟨g1, g2, g3⟩ := ih₂ ars hφ.2 U (norm φ U Γ).2
    refine ⟨letAtom_WF _ _, ?_, fun σ v₀ ρ hs hU i v => ?_⟩
    · rw [norm, letAtom_fv]
      intro n hn
      rcases List.mem_append.1 hn with hn | hn
      exacts [List.mem_append_left _ (h2 n hn), List.mem_append_right _ (g2 n hn)]
    simp only [norm]
    rw [letAtom_sat]
    set χ₁ := (norm φ U Γ).1
    set χ₂ := (norm ψ U (norm φ U Γ).2).1
    set xs := χ₁.fv ++ χ₂.fv
    have hiff := hs _ _ (envOf_last _ _) i (xs.map v) (by simp only [List.length_map]; rfl)
    rw [hiff]
    have hs₂ := letSem_prefix (List.prefix_append _ _) hs
    have hs₁ := letSem_prefix (norm_prefix ψ _ _) hs₂
    simp only [LBody.sem, MF.sat]
    refine exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ => ?_
    rw [Tr.sat_subst, Tr.sat_fv σ g1 _ _ v fun n hn =>
      vapp_ren xs v v₀ n (List.mem_append_right _ hn), g3 σ v₀ ρ hs₂ hU]
    refine and_congr_right fun _ => forall_congr' fun k => forall_congr' fun _ =>
      forall_congr' fun _ => ?_
    rw [Tr.sat_subst, Tr.sat_fv σ h1 _ _ v fun n hn =>
      vapp_ren xs v v₀ n (List.mem_append_left _ hn), h3 σ v₀ ρ hs₁ hU]
  | letin ar body rest ih₁ ih₂ =>
    intro ars hφ U Γ
    obtain ⟨hb, hcl, hr⟩ := hφ
    obtain ⟨h1, h2, h3⟩ := ih₁ ars hb U Γ
    set Γ₁ := (norm body U Γ).2 ++ [⟨ar, .now (norm body U Γ).1⟩]
    obtain ⟨g1, g2, g3⟩ := ih₂ (ar :: ars) hr ((norm body U Γ).2.length :: U) Γ₁
    refine ⟨g1, g2, fun σ v₀ ρ hs hU i v => ?_⟩
    simp only [norm, MF.sat]
    apply g3 σ v₀ _ hs
    have hsΓ₁ := letSem_prefix (norm_prefix rest _ _) hs
    intro k ar' hk
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
      refine ⟨_, rfl, fun j as has => ?_⟩
      simp only [List.getD_cons_zero]
      have hiff := hsΓ₁ _ _ (envOf_last _ _) j as has
      rw [hiff, LBody.sem, Tr.sat_fv σ h1 _ _ (vapp as v) fun n hn => ?_,
        h3 σ v₀ ρ (letSem_prefix (List.prefix_append _ _) hsΓ₁) hU]
      · simp [has]
      · have := hcl n (h2 n hn)
        rw [vapp_lt _ _ _ (by omega), vapp_lt _ _ _ (by omega)]
    | succ k =>
      obtain ⟨P, hP, hPi⟩ := hU k ar' (by simpa using hk)
      exact ⟨P, by simpa using hP, fun j as has => by simpa using hPi j as has⟩

  | agg k ω ts ys φ ih =>
    intro ars hφ U Γ
    obtain ⟨h1, h2, h3⟩ := ih ars hφ.1 U Γ
    set χ := (norm φ U Γ).1
    set xs := (χ.fv ++ ts.flatMap Term.supp).filterMap (shiftOut k) ++ ys
    have hxs : ∀ n, (n ∈ χ.fv ∨ ∃ t ∈ ts, n ∈ t.supp) → k ≤ n → n - k ∈ xs := by
      intro n hn hk
      refine List.mem_append_left _ (List.mem_filterMap.2 ⟨n, ?_, by
        simp [shiftOut, show ¬ n < k by omega]⟩)
      rcases hn with hn | ⟨t, ht, hn⟩
      · exact List.mem_append_left _ hn
      · exact List.mem_append_right _ (List.mem_flatMap.2 ⟨t, ht, hn⟩)
    refine ⟨letAtom_WF _ _, ?_, fun σ v₀ ρ hs hU i v => ?_⟩
    · show ∀ n ∈ (letAtom _ xs : Fm B ℕ D).fv, n ∈ _
      rw [letAtom_fv]
      intro n hn
      simp only [MF.fv]
      rcases List.mem_append.1 hn with hn | hn
      · refine List.mem_append_left _ ?_
        obtain ⟨m, hm, hmn⟩ := List.mem_filterMap.1 hn
        refine List.mem_filterMap.2 ⟨m, ?_, hmn⟩
        rcases List.mem_append.1 hm with hm | hm
        · exact List.mem_append_left _ (h2 m hm)
        · exact List.mem_append_right _ hm
      · exact List.mem_append_right _ hn
    show σ.sat i v (letAtom _ xs) ↔ _
    rw [letAtom_sat]
    have hiff := hs _ _ (envOf_last _ _) i (xs.map v) (by simp only [List.length_map]; rfl)
    rw [hiff]
    simp only [LBody.sem, MF.sat]
    have hren : ∀ n ∈ xs, (ren xs n).eval (vapp (xs.map v) v₀) = v n :=
      fun n hn => vapp_ren xs v v₀ n hn
    have hval : ∀ ds : List D, ds.length = k → ∀ n, (n ∈ χ.fv ∨ ∃ t ∈ ts, n ∈ t.supp) →
        (fun n => (upSn k (ren xs) n).eval (vapp ds (vapp (xs.map v) v₀))) n = vapp ds v n := by
      intro ds hl n hn
      subst hl
      rw [eval_upSn]
      by_cases hk : n < ds.length
      · rw [vapp_lt _ _ _ hk, vapp_lt _ _ _ hk]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + ds.length := ⟨n - ds.length, by omega⟩
        rw [vapp_ge, vapp_ge]
        exact hren m (by simpa using hxs (m + ds.length) hn (by omega))
    refine aggSem_congr (fun ds hl => ?_) (fun ds hl => ?_) ?_
    · rw [Tr.sat_subst, Tr.sat_fv σ h1 _ _ (vapp ds v) fun n hn => hval ds hl n (Or.inl hn),
        h3 σ v₀ ρ (letSem_prefix (List.prefix_append _ _) hs) hU]
    · rw [List.map_map]
      refine List.map_congr_left fun t ht => ?_
      simp only [Function.comp, Term.eval_subst]
      exact Term.eval_congr t (hφ.2 t ht) _ _ fun n hn => hval ds hl n (Or.inr ⟨t, ht, hn⟩)
    · rw [List.map_map]
      exact List.map_congr_left fun y hy => hren y (List.mem_append_right _ hy)

/-! ## Let order and let-normal form -/

/-- Let predicates referenced by a let body. -/
def LBody.lets {L : Type} : LBody B L D → List L
  | .now φ | .prev _ _ φ | .agg _ _ _ _ φ => φ.lets
  | .since _ _ φ ψ => φ.lets ++ ψ.lets

/-- Every let only refers to earlier lets. -/
def LetsOrdered (Γ : List (LetDef B ℕ D)) : Prop :=
  ∀ (p : ℕ) (d : LetDef B ℕ D), Γ[p]? = some d → ∀ q ∈ d.body.lets, q < p

theorem getElem?_append_last {Γ : List (LetDef B ℕ D)} {d d' : LetDef B ℕ D} {p : ℕ}
    (h : (Γ ++ [d])[p]? = some d') : (p < Γ.length ∧ Γ[p]? = some d') ∨ (p = Γ.length ∧ d' = d) := by
  rcases lt_or_ge p Γ.length with hp | hp
  · rw [List.getElem?_append_left hp] at h; exact Or.inl ⟨hp, h⟩
  · rw [List.getElem?_append_right hp] at h
    rcases List.getElem?_eq_some_iff.1 h with ⟨hl, he⟩
    simp at hl
    exact Or.inr ⟨by omega, by simpa [show p - Γ.length = 0 by omega] using he.symm⟩

theorem LetsOrdered.snoc {Γ : List (LetDef B ℕ D)} (h : LetsOrdered Γ) {d : LetDef B ℕ D}
    (hd : ∀ q ∈ d.body.lets, q < Γ.length) : LetsOrdered (Γ ++ [d]) := by
  intro p d' hp q hq
  rcases getElem?_append_last hp with ⟨-, hp⟩ | ⟨rfl, rfl⟩
  exacts [h p d' hp q hq, hd q hq]

/-- **Let order.**  Normalization keeps lets ordered, and the result only
    refers to existing lets. -/
theorem norm_ordered (φ : MF B D) : ∀ ars, φ.WF ars → ∀ U (Γ : List (LetDef B ℕ D)),
    U.length = ars.length → (∀ q ∈ U, q < Γ.length) → LetsOrdered Γ →
    LetsOrdered (norm φ U Γ).2 ∧ ∀ q ∈ (norm φ U Γ).1.lets, q < (norm φ U Γ).2.length := by
  induction φ with
  | tt | eq | pred => intro ars _ U Γ _ _ hΓ; exact ⟨hΓ, by simp [norm, Fm.lets]⟩
  | upred k ts =>
    intro ars hφ U Γ hU hq hΓ
    refine ⟨hΓ, fun q h => ?_⟩
    simp only [norm, Fm.lets, List.mem_singleton] at h; subst h
    have hk : k < U.length := by rw [hU]; exact (List.getElem?_eq_some_iff.1 hφ.1).1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    exact hq _ (List.getElem_mem hk)
  | neg φ ih | nx _ _ φ ih | ev _ _ φ ih =>
    intro ars hφ U Γ hU hq hΓ; exact ih ars hφ U Γ hU hq hΓ
  | conj φ ψ ih₁ ih₂ =>
    intro ars hφ U Γ hU hq hΓ
    obtain ⟨h1, h2⟩ := ih₁ ars hφ.1 U Γ hU hq hΓ
    obtain ⟨g1, g2⟩ := ih₂ ars hφ.2 U _ hU
      (fun q h => lt_of_lt_of_le (hq q h) (norm_prefix φ U Γ).length_le) h1
    refine ⟨g1, fun q h => ?_⟩
    rcases List.mem_append.1 h with h | h
    · exact lt_of_lt_of_le (h2 q h) (norm_prefix ψ _ _).length_le
    · exact g2 q h
  | ex φ ih =>
    intro ars hφ U Γ hU hq hΓ
    obtain ⟨h1, h2⟩ := ih ars hφ U Γ hU hq hΓ
    simp only [norm]
    split
    · refine ⟨h1.snoc fun q h => ?_, by simp [letAtom, Fm.lets]⟩
      simp only [LBody.lets, Fm.lets, Fm.lets_subst] at h; exact h2 q h
    · exact ⟨h1, h2⟩
  | prev a b φ ih =>
    intro ars hφ U Γ hU hq hΓ
    obtain ⟨h1, h2⟩ := ih ars hφ U Γ hU hq hΓ
    refine ⟨h1.snoc fun q h => ?_, by simp [norm, letAtom, Fm.lets]⟩
    simp only [LBody.lets, Fm.lets_subst] at h; exact h2 q h
  | agg k ω ts ys φ ih =>
    intro ars hφ U Γ hU hq hΓ
    obtain ⟨h1, h2⟩ := ih ars hφ.1 U Γ hU hq hΓ
    refine ⟨h1.snoc fun q h => ?_, by simp [norm, letAtom, Fm.lets]⟩
    simp only [LBody.lets, Fm.lets_subst] at h; exact h2 q h
  | since a b φ ψ ih₁ ih₂ =>
    intro ars hφ U Γ hU hq hΓ
    obtain ⟨h1, h2⟩ := ih₁ ars hφ.1 U Γ hU hq hΓ
    obtain ⟨g1, g2⟩ := ih₂ ars hφ.2 U _ hU
      (fun q h => lt_of_lt_of_le (hq q h) (norm_prefix φ U Γ).length_le) h1
    refine ⟨g1.snoc fun q h => ?_, by simp [norm, letAtom, Fm.lets]⟩
    simp only [LBody.lets, Fm.lets_subst, List.mem_append] at h
    rcases h with h | h
    · exact lt_of_lt_of_le (h2 q h) (norm_prefix ψ _ _).length_le
    · exact g2 q h
  | letin ar body rest ih₁ ih₂ =>
    intro ars hφ U Γ hU hq hΓ
    obtain ⟨h1, h2⟩ := ih₁ ars hφ.1 U Γ hU hq hΓ
    apply ih₂ (ar :: ars) hφ.2.2 _ _ (by simp [hU])
    · intro q h
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · have := lt_of_lt_of_le (hq q h) (norm_prefix body U Γ).length_le; simp; omega
    · exact h1.snoc fun q h => h2 q (by simpa [LBody.lets] using h)

/-- Every existential ranges over a formula with future operators. -/
def Fm.exFuture {L : Type} : Fm B L D → Prop
  | .ex φ => ¬ φ.present ∧ φ.exFuture
  | .neg φ | .ev _ _ φ | .nx _ _ φ => φ.exFuture
  | .conj φ ψ => φ.exFuture ∧ ψ.exFuture
  | .tt | .pred _ _ | .eq _ _ => True

theorem Fm.exFuture_subst {L : Type} (φ : Fm B L D) :
    ∀ s : ℕ → Term D, φ.exFuture → (φ.subst s).exFuture := by
  induction φ with
  | ex φ ih =>
    intro s h
    refine ⟨fun hp => h.1 ?_, ih _ h.2⟩
    rw [← Fm.isPresent_iff] at hp ⊢
    have : ∀ (ψ : Fm B L D) (s : ℕ → Term D), (ψ.subst s).isPresent = ψ.isPresent := by
      intro ψ; induction ψ with
      | conj a b iha ihb => intro s; simp [Fm.subst, Fm.isPresent, iha, ihb]
      | neg a iha | ex a iha => intro s; exact iha _
      | _ => intro s; rfl
    rwa [this] at hp
  | neg φ ih | ev _ _ φ ih | nx _ _ φ ih => intro s h; exact ih s h
  | conj φ ψ ih₁ ih₂ => intro s h; exact ⟨ih₁ s h.1, ih₂ s h.2⟩
  | _ => intro _ _; trivial

/-- Let-normal form (Section 4.1): past operators only occur at the top of let
    bodies (by construction of `Fm`), and existentials over present formulas
    only at the top of present let bodies. -/
def LBody.shape : LBody B ℕ D → Prop
  | .now φ => φ.exFuture ∨ ∃ ψ, φ = .ex ψ ∧ ψ.present ∧ ψ.exFuture
  | .since _ _ φ ψ => φ.exFuture ∧ ψ.exFuture
  | .prev _ _ φ | .agg _ _ _ _ φ => φ.exFuture

def LNF (Γ : List (LetDef B ℕ D)) (χ : Fm B ℕ D) : Prop :=
  χ.exFuture ∧ ∀ (p : ℕ) (d : LetDef B ℕ D), Γ[p]? = some d → d.body.shape

theorem LNF.snoc {Γ : List (LetDef B ℕ D)} (h : ∀ (p : ℕ) (d : LetDef B ℕ D), Γ[p]? = some d → d.body.shape)
    {d : LetDef B ℕ D} (hd : d.body.shape) :
    ∀ (p : ℕ) (d' : LetDef B ℕ D), (Γ ++ [d])[p]? = some d' → d'.body.shape := by
  intro p d' hp
  rcases getElem?_append_last hp with ⟨-, hp⟩ | ⟨rfl, rfl⟩
  exacts [h p d' hp, hd]

/-- **Let-normal form.** -/
theorem norm_shape (φ : MF B D) : ∀ U (Γ : List (LetDef B ℕ D)),
    (∀ (p : ℕ) (d : LetDef B ℕ D), Γ[p]? = some d → d.body.shape) → LNF (norm φ U Γ).2 (norm φ U Γ).1 := by
  induction φ with
  | tt | eq | pred | upred => intro U Γ hΓ; exact ⟨trivial, hΓ⟩
  | neg φ ih | nx _ _ φ ih | ev _ _ φ ih => intro U Γ hΓ; exact ih U Γ hΓ
  | conj φ ψ ih₁ ih₂ =>
    intro U Γ hΓ
    obtain ⟨h1, h2⟩ := ih₁ U Γ hΓ
    obtain ⟨g1, g2⟩ := ih₂ U _ h2
    exact ⟨⟨h1, g1⟩, g2⟩
  | ex φ ih =>
    intro U Γ hΓ
    obtain ⟨h1, h2⟩ := ih U Γ hΓ
    simp only [norm]
    split
    · rename_i hp
      refine ⟨trivial, LNF.snoc h2 (Or.inr ⟨_, rfl, ?_, Fm.exFuture_subst _ _ h1⟩)⟩
      exact Fm.present_subst _ _ ((Fm.isPresent_iff _).1 hp)
    · rename_i hp
      exact ⟨⟨fun h => hp ((Fm.isPresent_iff _).2 h), h1⟩, h2⟩
  | prev a b φ ih =>
    intro U Γ hΓ
    obtain ⟨h1, h2⟩ := ih U Γ hΓ
    exact ⟨trivial, LNF.snoc h2 (Fm.exFuture_subst _ _ h1)⟩
  | agg k ω ts ys φ ih =>
    intro U Γ hΓ
    obtain ⟨h1, h2⟩ := ih U Γ hΓ
    exact ⟨trivial, LNF.snoc h2 (Fm.exFuture_subst _ _ h1)⟩
  | since a b φ ψ ih₁ ih₂ =>
    intro U Γ hΓ
    obtain ⟨h1, h2⟩ := ih₁ U Γ hΓ
    obtain ⟨g1, g2⟩ := ih₂ U _ h2
    exact ⟨trivial, LNF.snoc g2 ⟨Fm.exFuture_subst _ _ h1, Fm.exFuture_subst _ _ g1⟩⟩
  | letin ar body rest ih₁ ih₂ =>
    intro U Γ hΓ
    obtain ⟨h1, h2⟩ := ih₁ U Γ hΓ
    exact ih₂ _ _ (LNF.snoc h2 (Or.inl h1))

/-! ## Present let operands -/

/-- Let bodies whose operands are present. -/
def LBody.presentOps {L : Type} : LBody B L D → Prop
  | .now φ | .prev _ _ φ | .agg _ _ _ _ φ => φ.present
  | .since _ _ φl φr => φl.present ∧ φr.present

theorem norm_present (φ : MF B D) (hφ : φ.ffree) :
    ∀ U (Γ : List (LetDef B ℕ D)), (norm φ U Γ).1.present := by
  induction φ with
  | tt | eq | pred | upred => intros; trivial
  | neg φ ih => intro U Γ; exact ih hφ U Γ
  | conj φ ψ ih₁ ih₂ => intro U Γ; exact ⟨ih₁ hφ.1 U Γ, ih₂ hφ.2 U _⟩
  | ex φ ih => intro U Γ; simp only [norm]; split
               · trivial
               · exact ih hφ U Γ
  | prev | since | agg => intros; trivial
  | nx | ev => exact absurd hφ id
  | letin ar body rest ih₁ ih₂ => intro U Γ; exact ih₂ hφ.2 _ _

/-- **Present let operands.**  If past operators and let bodies are
    future-free, every let operand is a present formula. -/
theorem norm_presentOps (φ : MF B D) (hφ : φ.PastPure) : ∀ U (Γ : List (LetDef B ℕ D)),
    (∀ (p : ℕ) (d : LetDef B ℕ D), Γ[p]? = some d → d.body.presentOps) →
    ∀ (p : ℕ) (d : LetDef B ℕ D), (norm φ U Γ).2[p]? = some d → d.body.presentOps := by
  have snoc : ∀ {Γ : List (LetDef B ℕ D)} {d : LetDef B ℕ D},
      (∀ (p : ℕ) (d : LetDef B ℕ D), Γ[p]? = some d → d.body.presentOps) → d.body.presentOps →
      ∀ (p : ℕ) (d' : LetDef B ℕ D), (Γ ++ [d])[p]? = some d' → d'.body.presentOps := by
    intro Γ d h hd p d' hp
    rcases getElem?_append_last hp with ⟨-, hp⟩ | ⟨rfl, rfl⟩
    exacts [h p d' hp, hd]
  induction φ with
  | tt | eq | pred | upred => intro U Γ hΓ; exact hΓ
  | neg φ ih | nx _ _ φ ih | ev _ _ φ ih => intro U Γ hΓ; exact ih hφ U Γ hΓ
  | conj φ ψ ih₁ ih₂ => intro U Γ hΓ; exact ih₂ hφ.2 U _ (ih₁ hφ.1 U Γ hΓ)
  | ex φ ih =>
    intro U Γ hΓ
    simp only [norm]
    split
    · rename_i hp
      exact snoc (ih hφ U Γ hΓ) (Fm.present_subst _ _ ((Fm.isPresent_iff _).1 hp))
    · exact ih hφ U Γ hΓ
  | prev a b φ ih =>
    intro U Γ hΓ
    exact snoc (ih hφ.2 U Γ hΓ) (Fm.present_subst _ _ (norm_present φ hφ.1 U Γ))
  | agg k ω ts ys φ ih =>
    intro U Γ hΓ
    exact snoc (ih hφ.2 U Γ hΓ) (Fm.present_subst _ _ (norm_present φ hφ.1 U Γ))
  | since a b φ ψ ih₁ ih₂ =>
    intro U Γ hΓ
    exact snoc (ih₂ hφ.2.2.2 U _ (ih₁ hφ.2.2.1 U Γ hΓ))
      ⟨Fm.present_subst _ _ (norm_present φ hφ.1 U Γ), Fm.present_subst _ _ (norm_present ψ hφ.2.1 U _)⟩
  | letin ar body rest ih₁ ih₂ =>
    intro U Γ hΓ
    exact ih₂ hφ.2.2 _ _ (snoc (ih₁ hφ.2.1 U Γ hΓ) (norm_present body hφ.1 U Γ))

end

/-! ## Let-normal form of a policy -/

/-- The let-normal form `(χ, Γ)` of a formula. -/
abbrev lnf (φ : MF B D) : Fm B ℕ D × List (LetDef B ℕ D) := norm φ [] []

/-- `χ` with lets `Γ` is equivalent to `φ`: on every trace interpreting the
    let predicates by `Γ`, they are satisfied at the same points. -/
def LetEquiv (φ : MF B D) (Γ : List (LetDef B ℕ D)) (χ : Fm B ℕ D) : Prop :=
  ∀ (σ : Tr B ℕ D) (v₀ : ℕ → D), LetSem (envOf Γ) σ v₀ → ∀ i v, σ.sat i v χ ↔ φ.sat σ [] i v

/-- **Let-normalization** (paper, Theorem 4.1): every
    well-formed MFOTL formula has an equivalent let-normal form. -/
theorem let_normal_form (φ : MF B D) (hφ : φ.WF []) :
    LNF (lnf φ).2 (lnf φ).1 ∧ LetEquiv φ (lnf φ).2 (lnf φ).1 :=
  ⟨norm_shape φ [] [] (by intro p d h; simp at h),
   fun σ v₀ h i v => (norm_correct φ [] hφ [] []).2.2 σ v₀ [] h (by intro k ar h; simp at h) i v⟩

end Enfflash
