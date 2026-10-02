/-
  `Eval` of the compiled items on a history.
-/
import Paper.Proof.Hist

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem atoms_gdisj (π : GDisj Voc) :
    π.toFormula.atoms = {a | ∃ κ ∈ π, a ∈ κ.toFormula.atoms} := by
  induction π with
  | nil => simp [GDisj.toFormula, Formula.bot, Formula.atoms]
  | cons κ π ih =>
    simp only [GDisj.toFormula, List.foldr_cons, Formula.or, Formula.atoms] at ih ⊢
    rw [ih]; ext a; simp

theorem atoms_prod_sub (π₁ π₂ : GDisj Voc) :
    (π₁.prod π₂).toFormula.atoms ⊆ π₁.toFormula.atoms ∪ π₂.toFormula.atoms := by
  rw [atoms_gdisj, atoms_gdisj, atoms_gdisj]
  rintro a ⟨κ, hκ, ha⟩
  simp only [GDisj.prod, List.mem_flatMap, List.mem_map] at hκ
  obtain ⟨κ₁, h₁, κ₂, h₂, rfl⟩ := hκ
  have : ∀ κ κ' : GConj Voc, (κ ++ κ').toFormula.atoms = κ.toFormula.atoms ∪ κ'.toFormula.atoms := by
    intro κ κ'
    induction κ with
    | nil => simp [GConj.toFormula, Formula.atoms]
    | cons γ κ ih =>
      simp only [List.cons_append, GConj.toFormula, List.foldr_cons, Formula.atoms] at ih ⊢
      rw [ih, Set.union_assoc]
  rw [this] at ha
  rcases ha with ha | ha
  · exact Or.inl ⟨κ₁, h₁, ha⟩
  · exact Or.inr ⟨κ₂, h₂, ha⟩

theorem GX.atoms_sub {m : Set Voc.ℰ} {p X Φ π φ} (h : GX m p X Φ π φ) :
    π.toFormula.atoms ⊆ Φ.atoms ∧ φ.atoms ⊆ Φ.atoms := by
  induction h with
  | none => simp [GDisj.toFormula, GConj.toFormula, Formula.or, Formula.bot, Formula.atoms]
  | vac => simp [GDisj.toFormula, Formula.bot, Formula.atoms]
  | pred => simp [GDisj.toFormula, GConj.toFormula, Formula.or, Formula.bot, Formula.atoms,
      GAtom.toFormula]
  | eq => simp [GDisj.toFormula, GConj.toFormula, Formula.or, Formula.bot, Formula.atoms,
      GAtom.toFormula]
  | andPos _ _ _ ih₁ ih₂ =>
    refine ⟨(atoms_prod_sub _ _).trans (Set.union_subset_union ih₁.1 ih₂.1), ?_⟩
    simp only [Formula.atoms]; exact Set.union_subset_union ih₁.2 ih₂.2
  | andNeg _ _ ih₁ ih₂ =>
    refine ⟨?_, ?_⟩
    · have : ∀ π₁ π₂ : GDisj Voc, (π₁ ++ π₂).toFormula.atoms =
          π₁.toFormula.atoms ∪ π₂.toFormula.atoms := by
        intro π₁ π₂; rw [atoms_gdisj, atoms_gdisj, atoms_gdisj]; ext a
        simp only [List.mem_append, Set.mem_setOf_eq, Set.mem_union]
        constructor
        · rintro ⟨κ, h | h, ha⟩
          · exact Or.inl ⟨κ, h, ha⟩
          · exact Or.inr ⟨κ, h, ha⟩
        · rintro (⟨κ, h, ha⟩ | ⟨κ, h, ha⟩)
          · exact ⟨κ, Or.inl h, ha⟩
          · exact ⟨κ, Or.inr h, ha⟩
      rw [this]; simp only [Formula.atoms]; exact Set.union_subset_union ih₁.1 ih₂.1
    · simp only [Formula.atoms, Formula.imp, Formula.or]
      exact Set.union_subset_union (Set.union_subset ih₁.1 ih₁.2) (Set.union_subset ih₂.1 ih₂.2)
  | neg _ ih => exact ih

theorem GuardClause.preds_sub {m : Set Voc.ℰ} {X : Set Voc.𝕍} {Φ : Formula Voc} {a : Clause Voc}
    {π : GDisj Voc} {ψ : Formula Voc} (hg : Guards m X Φ = some (π, ψ)) :
    (Formula.and π.toFormula ψ).preds ⊆ Φ.preds := by
  obtain ⟨h1, h2⟩ := (Guards_spec hg).atoms_sub
  simp only [Formula.preds, Formula.atoms, Set.image_union]
  exact Set.union_subset (Set.image_mono h1) (Set.image_mono h2)

/-- The rows of a compiled clause. -/
theorem rows_guard {R : Interpretation Voc} {S : Str Voc.toSignature} {j : ℕ}
    {m : Set Voc.ℰ} {X : Set Voc.𝕍} {Φ : Formula Voc} {a : Clause Voc}
    (ha : GuardClause m X Φ a) (hX : Φ.fv ⊆ X) (hR : ∀ q ∈ Φ.preds, R q = RelOf S j q)
    (xs : List Voc.𝕍) :
    rows R a xs = {r | ∃ v : Val Voc, v.dom = X ∧ Φ.sat S v j ∧ xs.mapM v = some r} := by
  obtain ⟨π, ψ, hg, hc⟩ := ha
  have hsem := clause_sem hR (GuardClause.preds_sub (a := a) hg) hc
  rw [trigSem_guards hg hX] at hsem
  ext r
  simp only [rows, hsem, Set.mem_setOf_eq, Val.proj]
  constructor
  · rintro ⟨v, ⟨h1, h2⟩, h3⟩; exact ⟨v, h1, h2, h3⟩
  · rintro ⟨v, h1, h2, h3⟩; exact ⟨v, ⟨h1, h2⟩, h3⟩

/-! ## Existential prefixes -/

theorem exs_sat (S : Str Voc.toSignature) (j : ℕ) (χ : Formula Voc) :
    ∀ (ys : List Voc.𝕍) (v : Val Voc), (Formula.exs ys χ).sat S v j ↔
      ∃ w : Val Voc, (∀ z, z ∉ ys → w z = v z) ∧ (∀ y ∈ ys, (w y).isSome) ∧ χ.sat S w j
  | [], v => by
    simp only [Formula.exs, List.foldr_nil, List.not_mem_nil, not_false_eq_true, forall_const,
      List.mem_nil_iff, false_imp_iff, implies_true, true_and]
    constructor
    · intro h; exact ⟨v, fun _ => rfl, h⟩
    · rintro ⟨w, hw, h⟩; rwa [show w = v from funext hw] at h
  | y :: ys, v => by
    rw [show Formula.exs (y :: ys) χ = .ex y (Formula.exs ys χ) from rfl]
    simp only [Formula.sat]
    constructor
    · rintro ⟨d, hd⟩
      obtain ⟨w, h1, h2, h3⟩ := (exs_sat S j χ ys _).1 hd
      refine ⟨w, fun z hz => ?_, fun y' hy' => ?_, h3⟩
      · simp only [List.mem_cons, not_or] at hz
        rw [h1 z hz.2, Val.upd_ne _ _ hz.1]
      · rcases List.mem_cons.1 hy' with rfl | hy'
        · by_cases hy : y' ∈ ys
          · exact h2 y' hy
          · rw [h1 y' hy]; simp
        · exact h2 y' hy'
    · rintro ⟨w, h1, h2, h3⟩
      obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (h2 y (by simp))
      refine ⟨d, (exs_sat S j χ ys _).2 ⟨w, fun z hz => ?_, fun y' hy' => h2 y' (by simp [hy']), h3⟩⟩
      by_cases hzy : z = y
      · subst hzy; simp [hd]
      · rw [Val.upd_ne _ _ hzy]; exact h1 z (by simp [hzy, hz])

theorem fv_exs (χ : Formula Voc) : ∀ ys : List Voc.𝕍, (Formula.exs ys χ).fv = χ.fv \ {x | x ∈ ys}
  | [] => by simp [Formula.exs]
  | y :: ys => by
    rw [show Formula.exs (y :: ys) χ = .ex y (Formula.exs ys χ) from rfl]
    simp only [Formula.fv, fv_exs χ ys]
    ext x; simp; tauto

theorem clean_exs (χ : Formula Voc) : ∀ (ys : List Voc.𝕍) (G : Set Voc.𝕍),
    (Formula.exs ys χ).Clean G → ∀ y ∈ ys, y ∉ G
  | [], _, _ => by simp
  | y :: ys, G, h => by
    rw [show Formula.exs (y :: ys) χ = .ex y (Formula.exs ys χ) from rfl] at h
    obtain ⟨hy, h⟩ := h
    intro y' hy'
    rcases List.mem_cons.1 hy' with rfl | hy'
    · exact hy
    · exact fun h' => clean_exs χ ys _ h y' hy' (Or.inl h')

theorem mapM_some_of_map {v : Val Voc} {xs : List Voc.𝕍} {r : List Voc.𝔻} :
    xs.mapM v = some r ↔ xs.map v = r.map some := mapM_eq_some v xs r

/-- The rows of a present let. -/
theorem present_rows (S : Str Voc.toSignature) (j : ℕ) {χ : Formula Voc} {ys xs : List Voc.𝕍}
    (hfv : (Formula.exs ys χ).fv = {x | x ∈ xs}) (hcl : (Formula.exs ys χ).Clean {x | x ∈ xs})
    (z0 : Voc.𝔻) :
    {r | ∃ v : Val Voc, v.dom = χ.fv ∧ χ.sat S v j ∧ xs.mapM v = some r} =
      {r | ∃ v' : Val Voc, v'.Covers (Formula.exs ys χ).fv ∧ xs.map v' = r.map some ∧
        (Formula.exs ys χ).sat S v' j} := by
  have hdis := clean_exs χ ys _ hcl
  rw [fv_exs] at hfv
  have hxs : ∀ x ∈ xs, x ∈ χ.fv := by
    intro x hx; have : x ∈ ({x | x ∈ xs} : Set Voc.𝕍) := hx
    rw [← hfv] at this; exact this.1
  have hχ : ∀ x ∈ χ.fv, x ∈ xs ∨ x ∈ ys := by
    intro x hx; by_cases hy : x ∈ ys
    · exact Or.inr hy
    · left; have : x ∈ χ.fv \ {x | x ∈ ys} := ⟨hx, hy⟩; rw [hfv] at this; exact this
  ext r
  simp only [Set.mem_setOf_eq, mapM_some_of_map]
  constructor
  · rintro ⟨v, hd, hs, hr⟩
    refine ⟨v, fun x hx => ?_, hr, (exs_sat S j χ ys v).2 ⟨fun z => if z ∈ ys then (v z).or (some z0) else v z,
      fun z hz => by simp [hz], fun y hy => by simp only [hy, ↓reduceIte]; cases v y <;> rfl, ?_⟩⟩
    · rw [fv_exs, hfv] at hx
      have : x ∈ v.dom := by rw [hd]; exact hxs x hx
      exact this
    · refine (Formula.sat_congr χ S _ v j fun z hz => ?_).2 hs
      by_cases hzy : z ∈ ys
      · have : z ∈ v.dom := by rw [hd]; exact hz
        obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 this
        simp [hzy, ha]
      · simp [hzy]
  · rintro ⟨v', hc, hr, hs⟩
    obtain ⟨w, h1, h2, h3⟩ := (exs_sat S j χ ys v').1 hs
    have hwx : ∀ x ∈ xs, w x = v' x := fun x hx => h1 x fun hy => hdis x hy hx
    have hcov : w.Covers χ.fv := by
      intro x hx
      rcases hχ x hx with hx' | hx'
      · rw [hwx x hx']; exact hc x (by rw [fv_exs, hfv]; exact hx')
      · exact h2 x hx'
    refine ⟨w.restrict χ.fv, Val.restrict_dom hcov,
      (Formula.sat_congr χ S _ w j fun z hz => Val.restrict_agree w _ z hz).2 h3, ?_⟩
    rw [← hr]
    exact List.map_congr_left fun x hx => by
      rw [Val.restrict_agree w _ x (hxs x hx), hwx x hx]

/-! ## Rows of a formula under the canonical valuation -/

/-- The tuples `r` for which `φ` (with free variables among `x̄`) holds. -/
def DefRows (S : Str Voc.toSignature) (j : ℕ) (φ : Formula Voc) (xs : List Voc.𝕍) :
    Set (List Voc.𝔻) :=
  {r | ∃ v' : Val Voc, v'.Covers φ.fv ∧ xs.map v' = r.map some ∧ φ.sat S v' j}

theorem rowsAt_iff {S : Str Voc.toSignature} {m : ℕ} {φ : Formula Voc} {xs : List Voc.𝕍}
    (hfv : φ.fv ⊆ {x | x ∈ xs}) {v : Val Voc} {r : List Voc.𝔻} (hv : xs.map v = r.map some) :
    r ∈ RowsAt S m φ xs ↔ φ.sat S v m := by
  constructor
  · rintro ⟨w, -, hw, hs⟩
    refine (Formula.sat_congr φ S w v m fun x hx => ?_).1 hs
    have hx' : x ∈ xs := hfv hx
    have := (List.map_inj_left.1 (hw.trans hv.symm)) x hx'
    exact this
  · intro hs
    exact ⟨v, covers_of_map hv, hv, hs⟩

theorem defRows_iff {S : Str Voc.toSignature} {j : ℕ} {φ : Formula Voc} {xs : List Voc.𝕍}
    (hfv : φ.fv = {x | x ∈ xs}) {v : Val Voc} {r : List Voc.𝔻} (hv : xs.map v = r.map some) :
    r ∈ DefRows S j φ xs ↔ φ.sat S v j := by
  constructor
  · rintro ⟨w, -, hw, hs⟩
    refine (Formula.sat_congr φ S w v j fun x hx => ?_).1 hs
    rw [hfv] at hx
    exact (List.map_inj_left.1 (hw.trans hv.symm)) x hx
  · intro hs
    exact ⟨v, by rw [hfv]; exact covers_of_map hv, hv, hs⟩

theorem len_of_map {v : Val Voc} {xs : List Voc.𝕍} {r : List Voc.𝔻} (h : xs.map v = r.map some) :
    r.length = xs.length := by
  have := congrArg List.length h; simpa using this.symm

theorem rowsAt_len {S : Str Voc.toSignature} {m : ℕ} {φ : Formula Voc} {xs : List Voc.𝕍}
    {r : List Voc.𝔻} (h : r ∈ RowsAt S m φ xs) : r.length = xs.length := by
  obtain ⟨v, -, hv, -⟩ := h; exact len_of_map hv

theorem defRows_len {S : Str Voc.toSignature} {j : ℕ} {φ : Formula Voc} {xs : List Voc.𝕍}
    {r : List Voc.𝔻} (h : r ∈ DefRows S j φ xs) : r.length = xs.length := by
  obtain ⟨v, -, hv, -⟩ := h; exact len_of_map hv

theorem rows_dom_eq {S : Str Voc.toSignature} {j : ℕ} {Φ : Formula Voc} {xs : List Voc.𝕍}
    (hfv : Φ.fv ⊆ {x | x ∈ xs}) :
    {r | ∃ v : Val Voc, v.dom = {x | x ∈ xs} ∧ Φ.sat S v j ∧ xs.mapM v = some r} =
      RowsAt S j Φ xs := by
  ext r
  simp only [Set.mem_setOf_eq, mapM_some_of_map, RowsAt]
  constructor
  · rintro ⟨v, hd, hs, hr⟩
    exact ⟨v, fun x hx => by have : x ∈ v.dom := hd ▸ hx; exact this, hr, hs⟩
  · rintro ⟨v, hc, hr, hs⟩
    refine ⟨v.restrict {x | x ∈ xs}, Val.restrict_dom hc,
      (Formula.sat_congr Φ S _ v j fun z hz => Val.restrict_agree v _ z (hfv hz)).2 hs, ?_⟩
    rw [← hr]; exact List.map_congr_left fun x hx => Val.restrict_agree v _ x hx

/-! ## Windows -/

theorem Interval.bounds_spec (I : Interval) :
    ∀ t, t ∈ I ↔ I.bounds.1 ≤ t ∧ (t : ℕ∞) ≤ I.bounds.2 := by
  intro t
  have hex := I.eq_icc
  unfold Interval.bounds
  rw [dif_pos hex]
  have h := hex.choose_spec.choose_spec.choose_spec
  conv_lhs => rw [h]
  rfl

theorem mem_window {s : Set (ℕ × List Voc.𝔻)} {τ : ℕ} {I : Interval} {r : List Voc.𝔻} :
    r ∈ window s τ I.bounds.1 I.bounds.2 ↔ ∃ τ', (τ', r) ∈ s ∧ τ' ≤ τ ∧ τ - τ' ∈ I := by
  simp only [window, Set.mem_setOf_eq, Interval.bounds_spec]

/-- **A table for `φ_l S_I φ_r`** (with `⧫ = ⊤ S`) computes the semantics of the
    since, both before and after its update at the current time-point. -/
theorem since_eval (S : Str Voc.toSignature) (j : ℕ) (I : Interval) (φl φr : Formula Voc)
    (xs : List Voc.𝕍) (hfvl : φl.fv ⊆ {x | x ∈ xs}) (hfvr : φr.fv ⊆ {x | x ∈ xs})
    (hfv : (Formula.since I φl φr).fv = {x | x ∈ xs})
    (hmono : ∀ m ≤ j, S.τ m ≤ S.τ j) (hnd : xs.Nodup)
    (T : Set (ℕ × List Voc.𝔻))
    (hT : T = {tr | ∃ m < j, tr.1 = S.τ m ∧ tr.2 ∈ RowsAt S m φr xs ∧
        ∀ m', m < m' → m' < j → tr.2 ∈ RowsAt S m' φl xs} ∨
      T = {tr | ∃ m < j + 1, tr.1 = S.τ m ∧ tr.2 ∈ RowsAt S m φr xs ∧
        ∀ m', m < m' → m' < j + 1 → tr.2 ∈ RowsAt S m' φl xs})
    (Rem : Set (List Voc.𝔻)) (hRem : Rem = RowsAt S j (.neg φl) xs) :
    (window T (S.τ j) I.bounds.1 I.bounds.2 \ Rem) ∪
        (if I.bounds.1 = 0 then RowsAt S j φr xs else ∅) =
      DefRows S j (.since I φl φr) xs := by
  subst hRem
  have h0 : 0 ∈ I ↔ I.bounds.1 = 0 := by rw [Interval.bounds_spec]; simp
  ext r
  by_cases hlen : r.length = xs.length
  · obtain ⟨v, hv, -⟩ := val_of_args xs r hnd hlen.symm
    have hrl : ∀ m, r ∈ RowsAt S m φl xs ↔ φl.sat S v m := fun m => rowsAt_iff hfvl hv
    have hrr : ∀ m, r ∈ RowsAt S m φr xs ↔ φr.sat S v m := fun m => rowsAt_iff hfvr hv
    have hrn : r ∈ RowsAt S j (.neg φl) xs ↔ ¬ φl.sat S v j := rowsAt_iff (φ := .neg φl) hfvl hv
    rw [defRows_iff hfv hv]
    simp only [Set.mem_union, Set.mem_diff, mem_window, hrn, not_not]
    simp only [Formula.sat]
    constructor
    · rintro (⟨⟨τ', hT', hle, hI⟩, hlj⟩ | hcur)
      · rcases hT with rfl | rfl
        · obtain ⟨m, hm, rfl, h1, h2⟩ := hT'
          exact ⟨m, hm.le, hI, (hrr m).1 h1, fun k hk1 hk2 => by
            rcases Nat.lt_or_eq_of_le hk2 with hk2 | rfl
            · exact (hrl k).1 (h2 k hk1 hk2)
            · exact hlj⟩
        · obtain ⟨m, hm, rfl, h1, h2⟩ := hT'
          exact ⟨m, by omega, hI, (hrr m).1 h1, fun k hk1 hk2 => by
            rcases Nat.lt_or_eq_of_le hk2 with hk2 | rfl
            · exact (hrl k).1 (h2 k hk1 (by omega))
            · exact hlj⟩
      · split_ifs at hcur with hb
        · exact ⟨j, le_rfl, by simp [h0, hb], (hrr j).1 hcur, fun k h1 h2 => absurd h2 (by omega)⟩
        · exact absurd hcur (Set.notMem_empty _)
    · rintro ⟨m, hm, hI, hr, hl⟩
      rcases Nat.lt_or_eq_of_le hm with hm | rfl
      · left
        refine ⟨⟨S.τ m, ?_, hmono m hm.le, hI⟩, hl j hm le_rfl⟩
        rcases hT with rfl | rfl
        · exact ⟨m, hm, rfl, (hrr m).2 hr, fun k h1 h2 => (hrl k).2 (hl k h1 h2.le)⟩
        · exact ⟨m, by omega, rfl, (hrr m).2 hr, fun k h1 h2 => (hrl k).2 (hl k h1 (by omega))⟩
      · right
        have : I.bounds.1 = 0 := h0.1 (by simpa using hI)
        simp only [this, ↓reduceIte]; exact (hrr m).2 hr
  · have hno : r ∉ DefRows S j (.since I φl φr) xs := fun h => hlen (defRows_len h)
    simp only [hno, iff_false, Set.mem_union, Set.mem_diff, not_or, not_and, not_not]
    refine ⟨fun h => ?_, ?_⟩
    · exfalso
      obtain ⟨τ', hT', -⟩ := mem_window.1 h
      rcases hT with rfl | rfl <;> (obtain ⟨m, -, -, h1, -⟩ := hT'; exact hlen (rowsAt_len h1))
    · split_ifs
      · exact fun h => hlen (rowsAt_len h)
      · simp

/-- **A lagged table for `●_I φ`** computes the semantics of the previous
    operator. -/
theorem prev_eval (S : Str Voc.toSignature) (j : ℕ) (I : Interval) (φ : Formula Voc)
    (xs : List Voc.𝕍) (hfvφ : φ.fv ⊆ {x | x ∈ xs}) (hfv : (Formula.prev I φ).fv = {x | x ∈ xs})
    (hmono : ∀ m ≤ j, S.τ m ≤ S.τ j) (hnd : xs.Nodup) (T : Set (ℕ × List Voc.𝔻))
    (hT : T = {tr | ∃ m, m + 1 = j ∧ tr.1 = S.τ m ∧ tr.2 ∈ RowsAt S m φ xs}) :
    window T (S.τ j) I.bounds.1 I.bounds.2 = DefRows S j (.prev I φ) xs := by
  subst hT
  ext r
  by_cases hlen : r.length = xs.length
  · obtain ⟨v, hv, -⟩ := val_of_args xs r hnd hlen.symm
    rw [defRows_iff hfv hv, mem_window]
    simp only [Formula.sat, Set.mem_setOf_eq]
    constructor
    · rintro ⟨τ', ⟨m, rfl, rfl, h1⟩, -, hI⟩
      exact ⟨by omega, by simpa using (rowsAt_iff hfvφ hv).1 h1, by simpa using hI⟩
    · rintro ⟨hj, h1, hI⟩
      refine ⟨S.τ (j - 1), ⟨j - 1, by omega, rfl, (rowsAt_iff hfvφ hv).2 h1⟩,
        hmono _ (by omega), hI⟩
  · have hno : r ∉ DefRows S j (.prev I φ) xs := fun h => hlen (defRows_len h)
    simp only [hno, iff_false, mem_window, not_exists, not_and]
    rintro τ' ⟨m, -, -, h1⟩; exact absurd (rowsAt_len h1) hlen

/-! ## Aggregations -/

theorem toVec_some {α : Type} {n : ℕ} {l : List α} {a : Fin n → α} :
    toVec n l = some a ↔ l = List.ofFn a := by
  unfold toVec
  constructor
  · intro h
    split_ifs at h with hl
    simp only [Option.some.injEq] at h; subst h
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2; simp
  · rintro rfl
    simp only [List.length_ofFn, ↓reduceDIte, Option.some.injEq]
    funext i; simp

theorem proj_some {v : Val Voc} {xs : List Voc.𝕍} {r : List Voc.𝔻} :
    v.proj xs = some r ↔ xs.map v = r.map some := mapM_eq_some v xs r

theorem mapM_id_map {xs : List Voc.𝕍} {v : Val Voc} {r : List Voc.𝔻} :
    (xs.map v).mapM id = some r ↔ xs.map v = r.map some := by
  rw [mapM_eq_some]; simp

/-- **An aggregation let** computes the semantics of the aggregation. -/
theorem agg_eval (S : Str Voc.toSignature) (j : ℕ) (R : Interpretation Voc) (T : Tables Voc)
    (τ : ℕ) (φ : Formula Voc) (ys gs xs : List Voc.𝕍) (ω : Voc.Ω) (ss : List (Term Voc))
    (c : Clause Voc) (ℓ : Option Label) (p : Voc.ℰ) (cols : List (Col Voc))
    (hc : c.sem R = {v | v.dom = φ.fv ∧ φ.sat S v j}) (hxs : xs = gs ++ ys)
    (hnd : (gs ++ ys).Nodup) (hys : ys.length = (Voc.ι' ω).2) :
    Eval (.agg ℓ p cols ω ss gs c) R T τ = DefRows S j (.agg ys ω ss gs φ) xs := by
  subst hxs
  have hfvagg : (Formula.agg ys ω ss gs φ).fv = {x | x ∈ gs ++ ys} := by
    simp only [Formula.fv]; ext x; simp
  have hdom : ∀ v : Val Voc, (∀ x, (v x).isSome ↔ x ∈ φ.fv) ↔ v.dom = φ.fv := by
    intro v; constructor
    · intro h; ext x; exact h x
    · intro h x; rw [← h]; rfl
  ext r
  simp only [Eval, hc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨vb, ⟨hvbd, hvbs⟩, gv, hgv, hfin, M, hM, w, hw, rfl⟩
    have hlen : (gs ++ ys).length = (gv ++ List.ofFn w).length := by
      have := len_of_map (proj_some.1 hgv); simp [this, hys]
    obtain ⟨v', hv', -⟩ := val_of_args (gs ++ ys) (gv ++ List.ofFn w) hnd hlen
    rw [List.map_append, List.map_append] at hv'
    have hgs : gs.map v' = gv.map some := by
      have := congrArg (List.take gs.length) hv'
      rwa [List.take_left' (by simp), List.take_left' (by simp [len_of_map (proj_some.1 hgv)])] at this
    have hysv : ys.map v' = (List.ofFn w).map some := by
      have := congrArg (List.drop gs.length) hv'
      rwa [List.drop_left' (by simp), List.drop_left' (by simp [len_of_map (proj_some.1 hgv)])] at this
    have hgrp : {v'' : Val Voc | (∀ x, (v'' x).isSome ↔ x ∈ φ.fv) ∧ gs.map v'' = gs.map v' ∧
        φ.sat S v'' j} = {v | (v.dom = φ.fv ∧ φ.sat S v j) ∧ gs.map v = gs.map vb} := by
      ext v''; simp only [Set.mem_setOf_eq, hdom, hgs, ← proj_some.1 hgv]; tauto
    refine ⟨v', by rw [hfvagg]; exact covers_of_map (by rw [List.map_append, List.map_append]; exact hv'),
      by rw [List.map_append, List.map_append]; exact hv', ?_⟩
    simp only [Formula.sat]
    rw [hgrp]
    refine ⟨⟨vb, ⟨hvbd, hvbs⟩, rfl⟩, hfin, M, hM, w, ?_, hw⟩
    rw [Option.bind_eq_some_iff]
    exact ⟨List.ofFn w, mapM_id_map.2 hysv, toVec_some.2 rfl⟩
  · rintro ⟨v', hc', hv', hs⟩
    simp only [Formula.sat] at hs
    obtain ⟨⟨vb, hvb1, hvb2, hvb3⟩, hfin, M, hM, y, hy, hyM⟩ := hs
    rw [Option.bind_eq_some_iff] at hy
    obtain ⟨l, hl, hly⟩ := hy
    rw [toVec_some] at hly; subst hly
    rw [mapM_id_map] at hl
    rw [List.map_append] at hv'
    have hcov : v'.Covers {x | x ∈ gs} := fun x hx => hc' x (by rw [hfvagg]; exact List.mem_append_left _ hx)
    obtain ⟨gv, hgv⟩ := mapM_isSome v' gs fun x hx => hcov x hx
    have hgvm := (mapM_eq_some _ _ _).1 hgv
    have hrsplit : r = gv ++ List.ofFn y := by
      have h1 : (gs.map v' ++ ys.map v') = (gv ++ List.ofFn y).map some := by
        rw [List.map_append, hgvm, hl]
      have h2 := hv'.symm.trans h1
      exact List.map_injective_iff.2 (Option.some_injective _) h2
    have hgrp : {v'' : Val Voc | (∀ x, (v'' x).isSome ↔ x ∈ φ.fv) ∧ gs.map v'' = gs.map v' ∧
        φ.sat S v'' j} = {v | (v.dom = φ.fv ∧ φ.sat S v j) ∧ gs.map v = gs.map vb} := by
      ext v''; simp only [Set.mem_setOf_eq, hdom, hvb2]; tauto
    refine ⟨vb, ⟨(hdom vb).1 hvb1, hvb3⟩, gv, ?_, hgrp ▸ hfin, M, ?_, y, hyM, hrsplit⟩
    · rw [proj_some, hvb2, hgvm]
    · rw [hM]; congr 2
      exact (Set.Finite.toFinset_inj).2 hgrp

end Paper
