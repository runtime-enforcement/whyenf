/-
  Local soundness of Figure 5 ("enforcing any alternative `C_k` enforces `φ`",
  l.1255–1257): if every clause of `C ∈ 𝒞` with `Γ ⊢ φ ↪^α 𝒞` is satisfied, then
  `φ` holds (`α = ℂ`) or fails (`α = 𝕊`).
-/
import Paper.Proof.Basic

namespace Paper

variable {Voc : Vocabulary}

/-! ## Satisfaction of clauses -/

/-- The variables of a clause. -/
def EClause.vars (c : EClause Voc) : Set Voc.𝕍 := c.trig.fv ∪ Term.varsList c.ε.args

/-- The effect `ε` holds for `w` at `i` in `S`.  A deferred `◇_[n,n] e(t̄)` holds
    at the time-point `dl(τᵢ + n)`, where `dl` gives the time-point at which the
    obligations of a timestamp are discharged; `○ⁿ e(t̄)` holds at `i + n`, and
    for `n = 1` the next time-point is at most one time unit later. -/
def Effect.Holds (S : Str Voc.toSignature) (dl : ℕ → ℕ) (w : Val Voc) (i : ℕ) :
    Effect Voc → Prop
  | .cau e ts => (Formula.pred e ts).sat S w i
  | .sup e ts => ¬ (Formula.pred e ts).sat S w i
  | .ev I e ts => ∀ n : ℕ, I = Interval.icc n n le_rfl →
      i ≤ dl (S.τ i + n) ∧ S.τ (dl (S.τ i + n)) = S.τ i + n ∧
        (Formula.pred e ts).sat S w (dl (S.τ i + n))
  | .nexts n e ts => (Formula.pred e ts).sat S w (i + n) ∧ (n = 1 → S.τ (i + 1) ≤ S.τ i + 1)

/-- `Θ` depends only on the variables `G`. -/
def DepOn (Θ : Val Voc → Prop) (G : Set Voc.𝕍) : Prop :=
  ∀ w w' : Val Voc, (∀ y ∈ G, w y = w' y) → (Θ w ↔ Θ w')

/-- The clause `c` is satisfied at `i` under the side condition `Θ`. -/
def SatRel (S : Str Voc.toSignature) (dl : ℕ → ℕ) (Θ : Val Voc → Prop) (c : EClause Voc)
    (i : ℕ) : Prop :=
  ∀ w : Val Voc, w.Covers c.vars → Θ w → c.trig.sat S w i → c.ε.Holds S dl w i

/-- The obligation events of the lets of `Γ` mean what they should:
    `Cau_e(ā)` implies `e(ā)` and `Sup_e(ā)` implies `¬e(ā)`. -/
def OblSem (Ξ : RwSetting Voc) (Γ : LetCtx Voc) (S : Str Voc.toSignature) : Prop :=
  ∀ e, (Γ e).isSome → ∀ i (ev : Event Voc.toSignature), ev ∈ S.D i →
    (ev.e = Ξ.cauN e → ∃ ev' ∈ S.D i, ev'.e = e ∧ ev'.args = ev.args) ∧
    (ev.e = Ξ.supN e → ∀ ev' ∈ S.D i, ev'.e = e → ev'.args ≠ ev.args)

/-! ## Lemmas -/

theorem sat_top_disj (S : Str Voc.toSignature) (w : Val Voc) (i : ℕ) :
    (GDisj.top : GDisj Voc).toFormula.sat S w i := by
  simp [GDisj.top, sat_disj, sat_conj]

theorem sat_single (S : Str Voc.toSignature) (w : Val Voc) (i : ℕ) (e : Voc.ℰ) (ts : List (Term Voc)) :
    (GDisj.toFormula ([[GAtom.pred e ts]] : GDisj Voc)).sat S w i ↔ (Formula.pred e ts).sat S w i := by
  simp [sat_disj, sat_conj, GAtom.toFormula]

theorem fv_top_disj : (GDisj.top : GDisj Voc).toFormula.fv = ∅ := by
  simp [GDisj.top, fv_gdisj, fv_gconj]

theorem fv_single (e : Voc.ℰ) (ts : List (Term Voc)) :
    (GDisj.toFormula ([[GAtom.pred e ts]] : GDisj Voc)).fv = Term.varsList ts := by
  simp [fv_gdisj, fv_gconj, GAtom.toFormula, Formula.fv]

theorem Formula.Clean.mono {φ : Formula Voc} : ∀ {G G' : Set Voc.𝕍}, φ.Clean G → G' ⊆ G → φ.Clean G' := by
  induction φ with
  | top | pred | eq | agg => intros; trivial
  | neg φ ih => exact fun h hG => ih h hG
  | and φ ψ ih₁ ih₂ =>
    exact fun h hG => ⟨ih₁ h.1 (Set.union_subset_union_left _ hG),
      ih₂ h.2 (Set.union_subset_union_left _ hG)⟩
  | ex x φ ih => exact fun h hG => ⟨fun hx => h.1 (hG hx), ih h.2 (Set.union_subset_union_left _ hG)⟩
  | next _ φ ih => exact fun h hG => ih h hG
  | prev _ φ ih => exact fun h hG => ih h hG
  | eventually _ φ ih => exact fun h hG => ih h hG
  | since _ φ ψ ih₁ ih₂ =>
    exact fun h hG => ⟨ih₁ h.1 (Set.union_subset_union_left _ hG),
      ih₂ h.2 (Set.union_subset_union_left _ hG)⟩
  | letin _ _ _ ψ _ ih₂ => exact fun h hG => ih₂ h hG

theorem Clean_nextN (φ : Formula Voc) (G : Set Voc.𝕍) : ∀ n, (nextN n φ).Clean G ↔ φ.Clean G
  | 0 => Iff.rfl
  | n + 1 => by
    rw [nextN, Function.iterate_succ_apply']; exact Clean_nextN φ G n

/-- The conjuncts other than `j`. -/
def others (φs : List (Formula Voc)) (j : Fin φs.length) : Formula Voc :=
  bigAnd ((List.finRange φs.length).filter (· ≠ j) |>.map fun i => φs[i])

theorem mem_others {φs : List (Formula Voc)} {j : Fin φs.length} {φ : Formula Voc} :
    φ ∈ ((List.finRange φs.length).filter (· ≠ j) |>.map fun i => φs[i]) ↔
      ∃ i : Fin φs.length, i ≠ j ∧ φs[i] = φ := by
  simp

theorem fv_others (φs : List (Formula Voc)) (j : Fin φs.length) :
    (others φs j).fv = {x | ∃ i : Fin φs.length, i ≠ j ∧ x ∈ φs[i].fv} := by
  simp only [others, fv_bigAnd, mem_others]
  ext x; simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨φ, ⟨i, hi, rfl⟩, hx⟩; exact ⟨i, hi, hx⟩
  · rintro ⟨i, hi, hx⟩; exact ⟨_, ⟨i, hi, rfl⟩, hx⟩

theorem sat_others (S : Str Voc.toSignature) (v : Val Voc) (k : ℕ) (φs : List (Formula Voc))
    (j : Fin φs.length) :
    (others φs j).sat S v k ↔ ∀ i : Fin φs.length, i ≠ j → φs[i].sat S v k := by
  simp only [others, sat_bigAnd, mem_others]
  constructor
  · intro h i hi; exact h _ ⟨i, hi, rfl⟩
  · rintro h φ ⟨i, hi, rfl⟩; exact h i hi

theorem sat_bigAnd_get (S : Str Voc.toSignature) (v : Val Voc) (k : ℕ) (φs : List (Formula Voc)) :
    (bigAnd φs).sat S v k ↔ ∀ i : Fin φs.length, φs[i].sat S v k := by
  rw [sat_bigAnd]
  constructor
  · intro h i; exact h _ (List.getElem_mem _)
  · intro h φ hφ
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hφ
    exact h ⟨i, hi⟩

theorem fv_get_sub_bigAnd (φs : List (Formula Voc)) (i : Fin φs.length) :
    φs[i].fv ⊆ (bigAnd φs).fv := by
  rw [fv_bigAnd]; intro x hx; exact ⟨_, List.getElem_mem _, hx⟩

/-- A clean conjunction has clean conjuncts, in the context of the others. -/
theorem Clean_bigAnd : ∀ {φs : List (Formula Voc)} {G : Set Voc.𝕍}, (bigAnd φs).Clean G →
    ∀ j : Fin φs.length, φs[j].Clean (G ∪ (others φs j).fv)
  | [], _, _, j => j.elim0
  | [φ], G, h, ⟨j, hj⟩ => by
    simp only [List.length_singleton, Nat.lt_one_iff] at hj; subst hj
    refine Formula.Clean.mono h (Set.union_subset le_rfl ?_)
    rw [fv_others]; rintro x ⟨⟨i, hi⟩, hne, -⟩
    simp only [List.length_singleton, Nat.lt_one_iff] at hi; subst hi
    exact absurd rfl hne
  | φ :: ψ :: φs, G, h, ⟨j, hj⟩ => by
    rw [show bigAnd (φ :: ψ :: φs) = .and φ (bigAnd (ψ :: φs)) from rfl] at h
    obtain ⟨h₁, h₂⟩ := h
    rcases j with _ | k
    · refine Formula.Clean.mono h₁ (Set.union_subset_union le_rfl ?_)
      rw [fv_others, fv_bigAnd]
      rintro x ⟨⟨_ | i, hi⟩, hne, hx⟩
      · exact absurd rfl hne
      · exact ⟨_, List.getElem_mem (l := ψ :: φs) (by simp at hi ⊢; omega), by simpa using hx⟩
    · have hk : k < (ψ :: φs).length := by simp at hj ⊢; omega
      have := Clean_bigAnd h₂ ⟨k, hk⟩
      refine Formula.Clean.mono (by simpa using this) ?_
      rintro x (hx | hx)
      · exact Or.inl (Or.inl hx)
      rw [fv_others] at hx ⊢
      obtain ⟨⟨_ | i, hi⟩, hne, hx⟩ := hx
      · exact Or.inl (Or.inr (by simpa using hx))
      · refine Or.inr ⟨⟨i, by simp at hi ⊢; omega⟩, fun h => hne ?_, by simpa using hx⟩
        simp [Fin.ext_iff] at h ⊢; omega

theorem Effect.holds_subst (S : Str Voc.toSignature) (dl : ℕ → ℕ) (w : Val Voc) (i : ℕ)
    (d : Voc.𝔻) (x : Voc.𝕍) (ε : Effect Voc) :
    (ε.subst d x).Holds S dl w i ↔ ε.Holds S dl (w.upd x d) i := by
  cases ε <;> simp [Effect.subst, Effect.Holds, Formula.sat, Term.evalList_subst]

/-- Extend a valuation to every variable. -/
def Val.ext (v : Val Voc) (d : Voc.𝔻) : Val Voc := fun y => (v y).or (some d)

theorem Val.ext_covers (v : Val Voc) (d : Voc.𝔻) (X : Set Voc.𝕍) : (v.ext d).Covers X := by
  intro y _; simp [Val.ext]

theorem Val.ext_agree {v : Val Voc} (d : Voc.𝔻) {X : Set Voc.𝕍} (h : v.Covers X) :
    ∀ y ∈ X, v.ext d y = v y := by
  intro y hy
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (h y hy)
  simp [Val.ext, ha]

theorem Val.Covers.mono {v : Val Voc} {X Y : Set Voc.𝕍} (h : v.Covers X) (hY : Y ⊆ X) : v.Covers Y :=
  fun y hy => h y (hY hy)

theorem Val.Covers.upd' {v : Val Voc} {X : Set Voc.𝕍} (h : v.Covers X) (x : Voc.𝕍) (d : Voc.𝔻) :
    (v.upd x d).Covers (X ∪ {x}) := by
  rintro y (hy | rfl)
  · by_cases hyx : y = x
    · subst hyx; simp
    · rw [Val.upd_ne _ _ hyx]; exact h y hy
  · simp

/-! ## The soundness statement -/

section
variable (Ξ : RwSetting Voc) (Γ : LetCtx Voc) (S : Str Voc.toSignature) (dl : ℕ → ℕ)

/-- The statement of local soundness for `Γ ⊢ φ ↪^α 𝒞`. -/
def RwSoundP (α : Mode) (φ : Formula Voc) (𝒞 : CSet Voc) : Prop :=
  ∀ C ∈ 𝒞, ∀ (G : Set Voc.𝕍) (Θ : Val Voc → Prop), DepOn Θ G → φ.Clean G →
    ∀ i (v : Val Voc), v.Covers (φ.fv ∪ G) → Θ v → (∀ c ∈ C, SatRel S dl Θ c i) →
      (α = .C → φ.sat S v i) ∧ (α = .S → ¬ φ.sat S v i)

theorem rw_sound_top : RwSoundP S dl .C .top {∅} := by
  intro _ _ _ _ _ _ _ _ _ _ _; exact ⟨fun _ => trivial, (fun h => nomatch h)⟩

theorem rw_sound_evC (e : Voc.ℰ) (ts : List (Term Voc)) :
    RwSoundP S dl .C (.pred e ts) {{⟨GDisj.top, .top, .cau e ts⟩}} := by
  intro C hC G Θ _ _ i v hv hΘ hsat
  rw [Set.mem_singleton_iff] at hC; subst hC
  refine ⟨fun _ => ?_, (fun h => nomatch h)⟩
  refine hsat _ rfl v (hv.mono ?_) hΘ ?_
  · simp [EClause.vars, EClause.trig, Formula.fv, fv_top_disj, Effect.args]
  · simp [EClause.trig, Formula.sat, sat_top_disj]

theorem rw_sound_evS (e : Voc.ℰ) (ts : List (Term Voc)) :
    RwSoundP S dl .S (.pred e ts) {{⟨[[.pred e ts]], .top, .sup e ts⟩}} := by
  intro C hC G Θ _ _ i v hv hΘ hsat
  rw [Set.mem_singleton_iff] at hC; subst hC
  refine ⟨(fun h => nomatch h), fun _ hp => ?_⟩
  refine hsat _ rfl v (hv.mono ?_) hΘ ?_ hp
  · simp [EClause.vars, EClause.trig, Formula.fv, fv_single, Effect.args]
  · simp only [EClause.trig, Formula.sat, sat_single]; exact ⟨hp, trivial⟩

variable {Ξ Γ S dl}

theorem rw_sound_letC (hOS : OblSem Ξ Γ S) (e : Voc.ℰ) (ts : List (Term Voc))
    (he : ∃ g s, Γ e = some (g, true, s)) :
    RwSoundP S dl .C (.pred e ts) {{⟨GDisj.top, .top, .cau (Ξ.cauN e) ts⟩}} := by
  intro C hC G Θ _ _ i v hv hΘ hsat
  rw [Set.mem_singleton_iff] at hC; subst hC
  refine ⟨fun _ => ?_, (fun h => nomatch h)⟩
  have h := hsat _ rfl v (hv.mono ?_) hΘ ?_
  · obtain ⟨ds, hds, ev, hev, hee, hea⟩ := h
    obtain ⟨g, s, hΓ⟩ := he
    obtain ⟨ev', hev', h1, h2⟩ := (hOS e (by simp [hΓ]) i ev hev).1 hee
    exact ⟨ds, hds, ev', hev', h1, h2.trans hea⟩
  · simp [EClause.vars, EClause.trig, Formula.fv, fv_top_disj, Effect.args]
  · simp [EClause.trig, Formula.sat, sat_top_disj]

theorem rw_sound_letS (hOS : OblSem Ξ Γ S) (e : Voc.ℰ) (ts : List (Term Voc))
    (he : ∃ g c, Γ e = some (g, c, true)) :
    RwSoundP S dl .S (.pred e ts) {{⟨[[.pred e ts]], .top, .cau (Ξ.supN e) ts⟩}} := by
  intro C hC G Θ _ _ i v hv hΘ hsat
  rw [Set.mem_singleton_iff] at hC; subst hC
  refine ⟨(fun h => nomatch h), fun _ hp => ?_⟩
  have h := hsat _ rfl v (hv.mono ?_) hΘ ?_
  · obtain ⟨ds, hds, ev, hev, hee, hea⟩ := h
    obtain ⟨g, c, hΓ⟩ := he
    obtain ⟨ds', hds', ev', hev', h1, h2⟩ := hp
    rw [hds] at hds'; cases hds'
    exact (hOS e (by simp [hΓ]) i ev hev).2 hee ev' hev' h1 (h2.trans hea.symm)
  · simp [EClause.vars, EClause.trig, Formula.fv, fv_single, Effect.args]
  · simp only [EClause.trig, Formula.sat, sat_single]; exact ⟨hp, trivial⟩

theorem rw_sound_neg {α : Mode} {φ : Formula Voc} {𝒞 : CSet Voc}
    (ih : RwSoundP S dl α.flip φ 𝒞) : RwSoundP S dl α (.neg φ) 𝒞 := by
  intro C hC G Θ hdep hcl i v hv hΘ hsat
  have := ih C hC G Θ hdep hcl i v hv hΘ hsat
  cases α
  · exact ⟨fun _ => this.2 rfl, (fun h => nomatch h)⟩
  · exact ⟨(fun h => nomatch h), fun _ h => h (this.1 rfl)⟩

theorem rw_sound_andS (φs : List (Formula Voc)) (j : Fin φs.length) {𝒞 : CSet Voc}
    (ih : RwSoundP S dl .S φs[j] 𝒞) :
    RwSoundP S dl .S (bigAnd φs)
      (𝒞.map fun π ψ ε => ⟨π, .and ψ (bigAnd ((List.finRange φs.length).filter (· ≠ j)
        |>.map fun i => φs[i])), ε⟩) := by
  intro C hC G Θ hdep hcl i v hv hΘ hsat
  obtain ⟨C₀, hC₀, rfl⟩ := hC
  refine ⟨(fun h => nomatch h), fun _ hall => ?_⟩
  set o := others φs j with ho
  have hall' := (sat_bigAnd_get S v i φs).1 hall
  let Θ' : Val Voc → Prop := fun w => Θ w ∧ w.Covers o.fv ∧ o.sat S w i
  have hdep' : DepOn Θ' (G ∪ o.fv) := by
    intro w w' hw
    have h1 := hdep w w' fun y hy => hw y (Or.inl hy)
    have h2 : ∀ y ∈ o.fv, w y = w' y := fun y hy => hw y (Or.inr hy)
    simp only [Θ', h1, Val.Covers]
    rw [Formula.sat_congr o S w w' i h2]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨a, fun y hy => (h2 y hy) ▸ b y hy, c⟩
    · rintro ⟨a, b, c⟩; exact ⟨a, fun y hy => (h2 y hy).symm ▸ b y hy, c⟩
  have hofv : o.fv ⊆ (bigAnd φs).fv := by
    rw [ho, fv_others]; rintro x ⟨k, -, hx⟩; exact fv_get_sub_bigAnd φs k hx
  refine (ih C₀ hC₀ (G ∪ o.fv) Θ' hdep' (Clean_bigAnd hcl j) i v ?_ ⟨hΘ, hv.mono ?_, ?_⟩ ?_).2 rfl
    (hall' j)
  · refine hv.mono (Set.union_subset (fv_get_sub_bigAnd φs j |>.trans Set.subset_union_left)
      (Set.union_subset Set.subset_union_right (hofv.trans Set.subset_union_left)))
  · exact hofv.trans Set.subset_union_left
  · exact (sat_others S v i φs j).2 fun k _ => hall' k
  · intro c hc w hw hΘw htr
    refine hsat _ ⟨c, hc, rfl⟩ w ?_ hΘw.1 ?_
    · simp only [EClause.vars, EClause.trig, Formula.fv] at hw ⊢
      rintro y ((hy | hy | hy) | hy)
      · exact hw y (Or.inl (Or.inl hy))
      · exact hw y (Or.inl (Or.inr hy))
      · exact hΘw.2.1 y hy
      · exact hw y (Or.inr hy)
    · simp only [EClause.trig, Formula.sat] at htr ⊢
      exact ⟨htr.1, htr.2, hΘw.2.2⟩

theorem rw_sound_andC (φs : List (Formula Voc)) (𝒞s : List (CSet Voc))
    (ih : List.Forall₂ (RwSoundP S dl .C) φs 𝒞s) :
    RwSoundP S dl .C (bigAnd φs) (CSet.bigTensor 𝒞s) := by
  intro C hC G Θ hdep hcl i v hv hΘ hsat
  refine ⟨fun _ => ?_, (fun h => nomatch h)⟩
  obtain ⟨Cs, hCs, hsub⟩ := mem_bigTensor hC
  have key : ∀ {φs : List (Formula Voc)} {𝒞s : List (CSet Voc)} {Cs : List (Set (EClause Voc))},
      List.Forall₂ (RwSoundP S dl .C) φs 𝒞s → List.Forall₂ (· ∈ ·) Cs 𝒞s → (∀ C' ∈ Cs, C' ⊆ C) →
      ∀ φ ∈ φs, ∃ 𝒞 C', RwSoundP S dl .C φ 𝒞 ∧ C' ∈ 𝒞 ∧ C' ⊆ C := by
    intro φs 𝒞s Cs h₁ h₂ h₃
    induction h₁ generalizing Cs with
    | nil => simp
    | cons hφ _ ih' =>
      cases h₂ with
      | cons hc hcs =>
        intro φ' hφ'
        rcases List.mem_cons.1 hφ' with rfl | hφ'
        · exact ⟨_, _, hφ, hc, h₃ _ (by simp)⟩
        · exact ih' hcs (fun C' hC' => h₃ C' (by simp [hC'])) φ' hφ'
  rw [sat_bigAnd]
  intro φ hφ
  obtain ⟨𝒞, C', hP, hC', hsub'⟩ := key ih hCs hsub φ hφ
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hφ
  refine (hP C' hC' G Θ hdep ((Clean_bigAnd hcl ⟨k, hk⟩).mono Set.subset_union_left) i v
    (hv.mono (Set.union_subset_union_left _ (fv_get_sub_bigAnd φs ⟨k, hk⟩))) hΘ
    fun c hc => hsat c (hsub' hc)).1 rfl

theorem rw_sound_exC (x : Voc.𝕍) {φ : Formula Voc} {𝒞 : CSet Voc}
    (hsub : ∀ C ∈ 𝒞, ∀ c ∈ C,
      (GDisj.subst Ξ.zero x c.π).isSome = true ∧ (Formula.subst Ξ.zero x c.ψ).isSome = true)
    (ih : RwSoundP S dl .C φ 𝒞) :
    RwSoundP S dl .C (.ex x φ) (𝒞.map fun π ψ ε =>
      ⟨(GDisj.subst Ξ.zero x π).getD π, (Formula.subst Ξ.zero x ψ).getD ψ, ε.subst Ξ.zero x⟩) := by
  intro C hC G Θ hdep hcl i v hv hΘ hsat
  obtain ⟨C₀, hC₀, rfl⟩ := hC
  refine ⟨fun _ => ⟨Ξ.zero, ?_⟩, (fun h => nomatch h)⟩
  obtain ⟨hxG, hcl'⟩ := hcl
  let Θ' : Val Voc → Prop := fun w => Θ w ∧ w x = some Ξ.zero
  have hdep' : DepOn Θ' (G ∪ {x}) := by
    intro w w' hw
    simp only [Θ', hdep w w' fun y hy => hw y (Or.inl hy), hw x (Or.inr rfl)]
  have hΘv : Θ (v.upd x Ξ.zero) := by
    refine (hdep _ _ fun y hy => ?_).1 hΘ
    rw [Val.upd_ne _ _ (fun h => hxG (by subst h; exact hy))]
  refine (ih C₀ hC₀ (G ∪ {x}) Θ' hdep' hcl' i (v.upd x Ξ.zero) ?_ ⟨hΘv, by simp⟩ ?_).1 rfl
  · refine (Val.Covers.upd' hv x Ξ.zero).mono ?_
    rintro y (hy | hy | hy)
    · by_cases hyx : y = x
      · exact Or.inr hyx
      · exact Or.inl (Or.inl ⟨hy, hyx⟩)
    · exact Or.inl (Or.inr hy)
    · exact Or.inr hy
  · intro c hc w hw hΘw htr
    obtain ⟨hπ, hψ⟩ := hsub C₀ hC₀ c hc
    obtain ⟨π', hπ'⟩ := Option.isSome_iff_exists.1 hπ
    obtain ⟨ψ', hψ'⟩ := Option.isSome_iff_exists.1 hψ
    obtain ⟨π1, π2⟩ := GDisj.subst_spec hπ'
    obtain ⟨ψ1, ψ2⟩ := Formula.subst_spec _ _ _ _ hψ'
    have hw0 : w.upd x Ξ.zero = w := Val.upd_eq_self w hΘw.2
    have := hsat _ ⟨c, hc, rfl⟩ w ?_ hΘw.1 ?_
    · simp only at this
      rw [Effect.holds_subst, hw0] at this; exact this
    · simp only [EClause.vars, EClause.trig, Formula.fv, hπ', hψ', Option.getD_some, π1, ψ1,
        Effect.subst_args, Term.varsList_subst] at hw ⊢
      intro y hy
      refine hw y ?_
      rcases hy with (hy | hy) | hy
      · exact Or.inl (Or.inl hy.1)
      · exact Or.inl (Or.inr hy.1)
      · exact Or.inr hy.1
    · simp only [EClause.trig, Formula.sat, hπ', hψ', Option.getD_some, π2, ψ2, hw0] at htr ⊢
      exact htr

theorem rw_sound_exS (x : Voc.𝕍) {φ : Formula Voc} {𝒞 : CSet Voc} (ih : RwSoundP S dl .S φ 𝒞) :
    RwSoundP S dl .S (.ex x φ)
      {D | ∃ C ∈ 𝒞, (∀ c ∈ C, ∃ π' ψ', TGX (Ξ.m Γ) .pos x c.π c.ψ π' ψ') ∧
        D = {c' | ∃ c ∈ C, TGX (Ξ.m Γ) .pos x c.π c.ψ c'.π c'.ψ ∧ c'.ε = c.ε}} := by
  intro C hC G Θ hdep hcl i v hv hΘ hsat
  obtain ⟨C₀, hC₀, hall, rfl⟩ := hC
  refine ⟨(fun h => nomatch h), fun _ ⟨d, hd⟩ => ?_⟩
  obtain ⟨hxG, hcl'⟩ := hcl
  have hΘv : Θ (v.upd x d) := by
    refine (hdep _ _ fun y hy => ?_).1 hΘ
    rw [Val.upd_ne _ _ (fun h => hxG (by subst h; exact hy))]
  refine (ih C₀ hC₀ G Θ hdep (hcl'.mono Set.subset_union_left) i (v.upd x d) ?_ hΘv ?_).2 rfl hd
  · refine (Val.Covers.upd' hv x d).mono ?_
    rintro y (hy | hy)
    · by_cases hyx : y = x
      · exact Or.inr hyx
      · exact Or.inl (Or.inl ⟨hy, hyx⟩)
    · exact Or.inl (Or.inr hy)
  · intro c hc w hw hΘw htr
    obtain ⟨π', ψ', ht⟩ := hall c hc
    obtain ⟨he, hfv, -⟩ := ht.spec
    have := hsat ⟨π', ψ', c.ε⟩ ⟨c, hc, ht, rfl⟩ w ?_ hΘw ?_
    · exact this
    · simp only [EClause.vars, EClause.trig] at hw ⊢
      exact hw.mono (Set.union_subset_union_left _ hfv)
    · simp only [EClause.trig] at htr ⊢
      exact (he S w i).2 htr

theorem rw_sound_futEv (a b : ℕ) (h : (a : ℕ∞) ≤ b) (d₀ : Voc.𝔻) {φ : Formula Voc} {𝒞 : CSet Voc}
    (ih : RwSoundP S dl .C φ 𝒞) :
    RwSoundP S dl .C (.eventually (Interval.icc a b h) φ)
      (CSet.map {C ∈ 𝒞 | C ≠ ∅ ∧ Uncond C} fun _ _ ε =>
        ⟨GDisj.top, .top, deferEffect (.ev (Interval.icc b b le_rfl)) ε⟩) := by
  intro C hC G Θ hdep hcl i v hv hΘ hsat
  obtain ⟨C₀, ⟨hC₀, hne, hun⟩, rfl⟩ := hC
  refine ⟨fun _ => ?_, (fun h => nomatch h)⟩
  obtain ⟨c₀, hc₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨⟨p, ts, hε⟩, -, -⟩ := hun c₀ hc₀
  have hagree := Val.ext_agree d₀ (hv.mono Set.subset_union_right)
  have hΘw : Θ (v.ext d₀) := (hdep _ _ fun y hy => hagree y hy).2 hΘ
  have h0 := hsat _ ⟨c₀, hc₀, rfl⟩ (v.ext d₀) (Val.ext_covers _ _ _) hΘw
    (by simp [EClause.trig, Formula.sat, sat_top_disj])
  simp only [hε, deferEffect, Effect.Holds] at h0
  obtain ⟨hij, hτ, -⟩ := h0 b rfl
  refine ⟨dl (S.τ i + b), hij, by simp [hτ]; exact_mod_cast h, ?_⟩
  refine (ih C₀ hC₀ G Θ hdep hcl _ v hv hΘ fun c hc w hw hΘ' _ => ?_).1 rfl
  obtain ⟨⟨p', ts', hε'⟩, hπ, hψ⟩ := hun c hc
  have := hsat _ ⟨c, hc, rfl⟩ w ?_ hΘ' (by simp [EClause.trig, Formula.sat, sat_top_disj])
  · simp only [hε', deferEffect, Effect.Holds] at this
    rw [hε']; exact (this b rfl).2.2
  · simp only [EClause.vars, EClause.trig, Formula.fv, fv_top_disj, hπ, hψ, hε', deferEffect,
      Effect.args] at hw ⊢
    exact hw

theorem rw_sound_futNext (b : ℕ∞) (d₀ : Voc.𝔻) {φ : Formula Voc} {𝒞 : CSet Voc} (hb : 1 ≤ b)
    (ih : RwSoundP S dl .C φ 𝒞) :
    RwSoundP S dl .C (.next (Interval.icc 0 b (by simp)) φ)
      (CSet.map {C ∈ 𝒞 | C ≠ ∅ ∧ Uncond C} fun _ _ ε =>
        ⟨GDisj.top, .top, deferEffect (.nexts 1) ε⟩) := by
  intro C hC G Θ hdep hcl i v hv hΘ hsat
  obtain ⟨C₀, ⟨hC₀, hne, hun⟩, rfl⟩ := hC
  refine ⟨fun _ => ?_, (fun h => nomatch h)⟩
  obtain ⟨c₀, hc₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨⟨p, ts, hε⟩, -, -⟩ := hun c₀ hc₀
  have hagree := Val.ext_agree d₀ (hv.mono Set.subset_union_right)
  have hΘw : Θ (v.ext d₀) := (hdep _ _ fun y hy => hagree y hy).2 hΘ
  have h0 := hsat _ ⟨c₀, hc₀, rfl⟩ (v.ext d₀) (Val.ext_covers _ _ _) hΘw
    (by simp [EClause.trig, Formula.sat, sat_top_disj])
  simp only [hε, deferEffect, Effect.Holds] at h0
  have hgap := h0.2 trivial
  refine ⟨?_, Interval.mem_icc.2 ⟨Nat.zero_le _,
    le_trans (by exact_mod_cast (show S.τ (i + 1) - S.τ i ≤ 1 by omega)) hb⟩⟩
  refine (ih C₀ hC₀ G Θ hdep hcl _ v hv hΘ fun c hc w hw hΘ' _ => ?_).1 rfl
  obtain ⟨⟨p', ts', hε'⟩, hπ, hψ⟩ := hun c hc
  have := hsat _ ⟨c, hc, rfl⟩ w ?_ hΘ' (by simp [EClause.trig, Formula.sat, sat_top_disj])
  · simp only [hε', deferEffect, Effect.Holds] at this
    rw [hε']; exact this.1
  · simp only [EClause.vars, EClause.trig, Formula.fv, fv_top_disj, hπ, hψ, hε', deferEffect,
      Effect.args] at hw ⊢
    exact hw

theorem rw_sound_futNextN (n : ℕ) {φ : Formula Voc} {𝒞 : CSet Voc} (ih : RwSoundP S dl .C φ 𝒞) :
    RwSoundP S dl .C (nextN n φ)
      (CSet.map {C ∈ 𝒞 | Uncond C} fun _ _ ε => ⟨GDisj.top, .top, deferEffect (.nexts n) ε⟩) := by
  intro C hC G Θ hdep hcl i v hv hΘ hsat
  obtain ⟨C₀, ⟨hC₀, hun⟩, rfl⟩ := hC
  refine ⟨fun _ => ?_, (fun h => nomatch h)⟩
  rw [sat_nextN]
  rw [Clean_nextN] at hcl; rw [fv_nextN] at hv
  refine (ih C₀ hC₀ G Θ hdep hcl _ v hv hΘ fun c hc w hw hΘ' _ => ?_).1 rfl
  obtain ⟨⟨p', ts', hε'⟩, hπ, hψ⟩ := hun c hc
  have := hsat _ ⟨c, hc, rfl⟩ w ?_ hΘ' (by simp [EClause.trig, Formula.sat, sat_top_disj])
  · simp only [hε', deferEffect, Effect.Holds] at this
    rw [hε']; exact this.1
  · simp only [EClause.vars, EClause.trig, Formula.fv, fv_top_disj, hπ, hψ, hε', deferEffect,
      Effect.args] at hw ⊢
    exact hw

/-- **Local soundness of Figure 5.** -/
theorem rw_sound (hOS : OblSem Ξ Γ S) {α : Mode} {φ : Formula Voc} {𝒞 : CSet Voc}
    (h : Rw Ξ Γ α φ 𝒞) : RwSoundP S dl α φ 𝒞 := by
  refine Rw.rec (motive_1 := fun α φ 𝒞 _ => RwSoundP S dl α φ 𝒞)
    (motive_2 := fun φs 𝒞s _ => List.Forall₂ (RwSoundP S dl .C) φs 𝒞s)
    (rw_sound_top S dl) (fun e ts _ => rw_sound_evC S dl e ts)
    (fun e ts _ => rw_sound_evS S dl e ts) (fun e ts he => rw_sound_letC hOS e ts he)
    (fun e ts he => rw_sound_letS hOS e ts he) (fun _ ih => rw_sound_neg ih)
    (fun φs j _ _ _ _ ih => rw_sound_andS φs j ih) (fun φs 𝒞s _ _ ih => rw_sound_andC φs 𝒞s ih)
    (fun x _ _ _ hsub ih => rw_sound_exC x hsub ih) (fun x _ _ _ ih => rw_sound_exS x ih)
    (fun a b h _ _ _ _ ih => rw_sound_futEv a b h Ξ.zero ih)
    (fun b _ _ _ hb ih => rw_sound_futNext b Ξ.zero hb ih)
    (fun n _ _ _ _ ih => rw_sound_futNextN n ih) .nil (fun _ _ ih ihs => .cons ih ihs) h

end

end Paper
