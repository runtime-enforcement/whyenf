/-
  EF clauses (Figure 3, `⟦·⟧_R`) and the MFOTL triggers they are compiled from.
-/
import Paper.Proof.Final

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-- The tuples of the `q`-events of `S` at `j`. -/
def RelOf (S : Str Voc.toSignature) (j : ℕ) (q : Voc.ℰ) : Set (List Voc.𝔻) :=
  {a | ∃ ev ∈ S.D j, ev.e = q ∧ ev.args = a}

/-- Restriction of a valuation. -/
noncomputable def Val.restrict (v : Val Voc) (X : Set Voc.𝕍) : Val Voc :=
  fun y => if y ∈ X then v y else none

theorem Val.restrict_dom {v : Val Voc} {X : Set Voc.𝕍} (h : v.Covers X) : (v.restrict X).dom = X := by
  ext y; simp only [Val.dom, Val.restrict, Set.mem_setOf_eq]
  by_cases hy : y ∈ X <;> simp [hy, h y]

theorem Val.restrict_agree (v : Val Voc) (X : Set Voc.𝕍) : ∀ y ∈ X, v.restrict X y = v y := by
  intro y hy; simp [Val.restrict, hy]

/-- A predicate on valuations that only depends on `X`. -/
def Local (P : Val Voc → Prop) (X : Set Voc.𝕍) : Prop :=
  ∀ v w : Val Voc, (∀ y ∈ X, v y = w y) → (P v ↔ P w)

theorem join_char {X Y : Set Voc.𝕍} {P Q : Val Voc → Prop} (hP : Local P X) (hQ : Local Q Y) :
    join {v | v.dom = X ∧ P v} {v | v.dom = Y ∧ Q v} = {u | u.dom = X ∪ Y ∧ P u ∧ Q u} := by
  ext u
  simp only [join, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, ⟨hv, hPv⟩, w, ⟨hw, hQw⟩, hc, rfl⟩
    have hagv : ∀ y ∈ X, v.union w y = v y := by
      intro y hy
      have : (v y).isSome := by rw [← hv] at hy; exact hy
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 this
      simp [Val.union, ha]
    have hagw : ∀ y ∈ Y, v.union w y = w y := by
      intro y hy
      have : (w y).isSome := by rw [← hw] at hy; exact hy
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 this
      cases hvy : v y with
      | none => simp [Val.union, hvy]
      | some a => simp [Val.union, hvy, hb, hc y a b hvy hb]
    refine ⟨?_, (hP _ _ hagv).2 hPv, (hQ _ _ hagw).2 hQw⟩
    ext y; simp only [Val.dom, Val.union, Set.mem_setOf_eq, Set.mem_union]
    rw [← hv, ← hw]; simp only [Val.dom, Set.mem_setOf_eq]
    cases v y <;> cases w y <;> simp
  · rintro ⟨hu, hPu, hQu⟩
    have hcX : u.Covers X := fun y hy => by
      have : y ∈ u.dom := hu ▸ Or.inl hy; exact this
    have hcY : u.Covers Y := fun y hy => by
      have : y ∈ u.dom := hu ▸ Or.inr hy; exact this
    refine ⟨u.restrict X, ⟨Val.restrict_dom hcX, (hP _ _ fun y hy => Val.restrict_agree u X y hy).2 hPu⟩,
      u.restrict Y, ⟨Val.restrict_dom hcY, (hQ _ _ fun y hy => Val.restrict_agree u Y y hy).2 hQu⟩,
      ?_, ?_⟩
    · intro y a b ha hb
      simp only [Val.restrict] at ha hb
      split_ifs at ha hb; rw [ha] at hb; exact Option.some.inj hb
    · funext y
      simp only [Val.union, Val.restrict]
      by_cases hX : y ∈ X
      · simp only [hX, ↓reduceIte]; cases u y <;> simp
      · by_cases hY : y ∈ Y
        · simp [hX, hY]
        · simp only [hX, hY, ↓reduceIte, Option.none_or]
          have : y ∉ u.dom := by rw [hu]; simp [hX, hY]
          simpa [Val.dom] using this

theorem local_sat (S : Str Voc.toSignature) (j : ℕ) (φ : Formula Voc) :
    Local (fun v => φ.sat S v j) φ.fv := fun v w h => Formula.sat_congr φ S v w j h

/-! ## Atoms and guards -/

theorem toGArg_spec {t : Term Voc} {g : GArg Voc} (h : t.toGArg = some g) :
    (∀ v, g.eval v = t.eval v) ∧ g.vars = t.vars := by
  cases t with
  | var x => simp [Term.toGArg] at h; subst h; exact ⟨fun _ => rfl, rfl⟩
  | const c => simp [Term.toGArg] at h; subst h; exact ⟨fun _ => rfl, by simp [GArg.vars, Term.vars]⟩
  | app => simp [Term.toGArg] at h

theorem toGArgs_spec : ∀ {ts : List (Term Voc)} {gs : List (GArg Voc)},
    List.Forall₂ (fun t g => t.toGArg = some g) ts gs →
      (∀ v, gs.mapM (GArg.eval v) = Term.evalList v ts) ∧
        {x | ∃ a ∈ gs, x ∈ a.vars} = Term.varsList ts
  | [], [], .nil => by simp [Term.evalList, Term.varsList]
  | t :: ts, g :: gs, .cons h hs => by
    obtain ⟨h1, h2⟩ := toGArg_spec h
    obtain ⟨i1, i2⟩ := toGArgs_spec hs
    refine ⟨fun v => ?_, ?_⟩
    · simp only [List.mapM_cons, Term.evalList, h1 v, i1 v]
    · rw [Term.varsList, ← i2, ← h2]; ext x; simp

theorem atom_sem {R : Interpretation Voc} {S : Str Voc.toSignature} {j : ℕ} {N : Set Voc.ℰ}
    (hR : ∀ q ∈ N, R q = RelOf S j q) {γ : GAtom Voc} (hγ : γ.toFormula.preds ⊆ N) {a : Atom Voc}
    (h : γ.toAtom = some a) :
    a.sem R = {v | v.dom = γ.toFormula.fv ∧ γ.toFormula.sat S v j} := by
  cases γ with
  | pred p ts =>
    simp only [GAtom.toAtom, Option.map_eq_some_iff] at h
    obtain ⟨gs, hgs, rfl⟩ := h
    obtain ⟨h1, h2⟩ := toGArgs_spec (mapM_forall₂ hgs)
    have hp : p ∈ N := hγ ⟨(p, ts), by simp [GAtom.toFormula, Formula.atoms], rfl⟩
    ext v
    simp only [Atom.sem, Atom.vars, h2, h1, Set.mem_setOf_eq, GAtom.toFormula, Formula.fv,
      Formula.sat, hR p hp, RelOf]
  | eq x c =>
    simp only [GAtom.toAtom, Option.some.injEq] at h; subst h
    ext v
    simp only [Atom.sem, Set.mem_singleton_iff, Set.mem_setOf_eq, GAtom.toFormula, Formula.fv,
      Formula.sat]
    constructor
    · rintro rfl
      refine ⟨?_, by simp⟩
      ext y; by_cases hy : y = x
      · subst hy; simp [Val.dom]
      · simp [Val.dom, Val.upd_ne _ _ hy, Val.empty, hy]
    · rintro ⟨hd, hx⟩
      funext y
      by_cases hy : y = x
      · subst hy; simp [hx]
      · rw [Val.upd_ne _ _ hy]
        have : y ∉ v.dom := by rw [hd]; simpa using hy
        simpa [Val.dom, Val.empty] using this

theorem local_and {P Q : Val Voc → Prop} {X Y : Set Voc.𝕍} (hP : Local P X) (hQ : Local Q Y) :
    Local (fun v => P v ∧ Q v) (X ∪ Y) := fun v w h =>
  and_congr (hP v w fun y hy => h y (Or.inl hy)) (hQ v w fun y hy => h y (Or.inr hy))

theorem foldl_join {R : Interpretation Voc} {S : Str Voc.toSignature} {j : ℕ} {N : Set Voc.ℰ}
    (hR : ∀ q ∈ N, R q = RelOf S j q) :
    ∀ {κ : GConj Voc} {as : List (Atom Voc)}, List.Forall₂ (fun γ a => γ.toAtom = some a) κ as →
      (∀ γ ∈ κ, γ.toFormula.preds ⊆ N) →
      ∀ (X₀ : Set Voc.𝕍) (P₀ : Val Voc → Prop), Local P₀ X₀ →
        as.foldl (fun A a => join A (a.sem R)) {v | v.dom = X₀ ∧ P₀ v} =
          {v | v.dom = X₀ ∪ κ.toFormula.fv ∧ P₀ v ∧ κ.toFormula.sat S v j}
  | [], [], .nil, _, X₀, P₀, _ => by
    ext v; simp [GConj.toFormula, Formula.fv, Formula.sat]
  | γ :: κ, a :: as, .cons h hs, hN, X₀, P₀, hP => by
    simp only [List.foldl_cons]
    rw [atom_sem hR (hN γ (by simp)) h, join_char hP (local_sat S j _),
      foldl_join hR hs (fun γ' hγ' => hN γ' (by simp [hγ'])) (X₀ ∪ γ.toFormula.fv) _
        (local_and hP (local_sat S j _))]
    ext v
    simp only [Set.mem_setOf_eq, GConj.toFormula, List.foldr_cons, Formula.fv, Formula.sat]
    rw [Set.union_assoc]; tauto

/-- The EF guard `κ` denotes the valuations on the variables of `κ` that satisfy it. -/
theorem guard_sem {R : Interpretation Voc} {S : Str Voc.toSignature} {j : ℕ} {N : Set Voc.ℰ}
    (hR : ∀ q ∈ N, R q = RelOf S j q) {κ : GConj Voc} (hN : ∀ γ ∈ κ, γ.toFormula.preds ⊆ N)
    {as : List (Atom Voc)}
    (h : κ.mapM GAtom.toAtom = some as) {κ' : EGuard Voc} (h' : toNList as = some κ') :
    κ'.sem R = {v | v.dom = κ.toFormula.fv ∧ κ.toFormula.sat S v j} := by
  have hf := mapM_forall₂ h
  cases as with
  | nil => simp [toNList] at h'
  | cons a as =>
    simp only [toNList, Option.some.injEq] at h'; subst h'
    cases hf with
    | @cons γ _ κ _ hγ hs =>
      simp only [EGuard.sem]
      have := foldl_join hR hs (fun γ' hγ' => hN γ' (by simp [hγ'])) γ.toFormula.fv
        (fun v => γ.toFormula.sat S v j) (local_sat S j _)
      rw [atom_sem hR (hN γ (by simp)) hγ]
      refine this.trans ?_
      ext v
      simp [GConj.toFormula, Formula.fv, Formula.sat]

/-! ## Filters and clauses -/

theorem filter_spec {R : Interpretation Voc} {S : Str Voc.toSignature} {j : ℕ} {N : Set Voc.ℰ}
    (hR : ∀ q ∈ N, R q = RelOf S j q) :
    ∀ {ψ : Formula Voc} {f : Filter Voc}, ψ.preds ⊆ N → ψ.toFilter = some f →
      (∀ v, f.holds R v ↔ ψ.sat S v j) ∧ f.fv = ψ.fv
  | .top, f, _, h => by
    simp [Formula.toFilter] at h; subst h; simp [Filter.holds, Formula.sat, Filter.fv, Formula.fv]
  | .pred p ts, f, hN, h => by
    simp [Formula.toFilter] at h; subst h
    have hp : p ∈ N := hN ⟨(p, ts), by simp [Formula.atoms], rfl⟩
    refine ⟨fun v => ?_, rfl⟩
    simp only [Filter.holds, Formula.sat, hR p hp, RelOf, Set.mem_setOf_eq]
  | .neg ψ, f, hN, h => by
    simp only [Formula.toFilter, Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨f', hf', rfl⟩ := h
    obtain ⟨h1, h2⟩ := filter_spec (ψ := ψ) hR hN hf'
    exact ⟨fun v => by simp only [Filter.holds, Formula.sat, h1], h2⟩
  | .and ψ χ, f, hN, h => by
    simp only [Formula.toFilter] at h
    cases h₁ : ψ.toFilter <;> cases h₂ : χ.toFilter <;>
      simp [h₁, h₂, Seq.seq, Option.map_eq_map] at h
    subst h
    have hN1 : ψ.preds ⊆ N := fun q hq => hN (by
      simp only [Formula.preds, Formula.atoms, Set.image_union]; exact Or.inl hq)
    have hN2 : χ.preds ⊆ N := fun q hq => hN (by
      simp only [Formula.preds, Formula.atoms, Set.image_union]; exact Or.inr hq)
    obtain ⟨a1, a2⟩ := filter_spec hR hN1 h₁
    obtain ⟨b1, b2⟩ := filter_spec hR hN2 h₂
    exact ⟨fun v => by simp only [Filter.holds, Formula.sat, a1, b1], by
      simp only [Filter.fv, Formula.fv, a2, b2]⟩
  | .ex .., _, _, h | .next .., _, _, h | .prev .., _, _, h | .eventually .., _, _, h
  | .since .., _, _, h | .letin .., _, _, h | .agg .., _, _, h | .eq .., _, _, h => by
    simp [Formula.toFilter] at h

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | [], [], .nil, a, ha => by simp at ha
  | a :: l, b' :: l', .cons h hs, a', ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b', by simp, h⟩
    · obtain ⟨b, h1, h2⟩ := forall₂_mem_left hs a' ha; exact ⟨b, by simp [h1], h2⟩

theorem atoms_gdisj_sub (π : GDisj Voc) :
    ∀ κ ∈ π, ∀ γ ∈ κ, γ.toFormula.atoms ⊆ π.toFormula.atoms := by
  induction π with
  | nil => simp
  | cons κ π ih =>
    intro κ' hκ' γ hγ a ha
    simp only [GDisj.toFormula, List.foldr_cons, Formula.or, Formula.atoms] at ih ⊢
    rcases List.mem_cons.1 hκ' with rfl | hκ'
    · left
      clear ih hκ'
      induction κ' with
      | nil => simp at hγ
      | cons γ' κ' ih' =>
        simp only [GConj.toFormula, List.foldr_cons, Formula.atoms] at ih' ⊢
        rcases List.mem_cons.1 hγ with rfl | hγ
        · exact Or.inl ha
        · exact Or.inr (ih' hγ)
    · right; exact ih κ' hκ' γ hγ ha

/-- The valuations that fire the compiled trigger `(π, ψ)`. -/
def TrigSem (S : Str Voc.toSignature) (j : ℕ) (π : GDisj Voc) (ψ : Formula Voc) : Set (Val Voc) :=
  match π with
  | [[]] => {v | v.dom = ψ.fv ∧ ψ.sat S v j}
  | _ => {v | (∃ κ ∈ π, v.dom = κ.toFormula.fv ∧ κ.toFormula.sat S v j) ∧ ψ.sat S v j}

theorem toNList_toList {α : Type} {l : List α} {n : NList α} (h : toNList l = some n) :
    n.toList = l := by
  cases l with
  | nil => simp [toNList] at h
  | cons a l => simp [toNList] at h; subst h; rfl

theorem clause_sem {R : Interpretation Voc} {S : Str Voc.toSignature} {j : ℕ} {N : Set Voc.ℰ}
    (hR : ∀ q ∈ N, R q = RelOf S j q) {π : GDisj Voc} {ψ : Formula Voc}
    (hN : (Formula.and π.toFormula ψ).preds ⊆ N) {cl : Clause Voc}
    (h : toClause π ψ = some cl) : cl.sem R = TrigSem S j π ψ := by
  have hψ : ψ.preds ⊆ N := fun q hq => hN (by
    simp only [Formula.preds, Formula.atoms, Set.image_union]; exact Or.inr hq)
  have hκN : ∀ κ ∈ π, ∀ γ ∈ κ, γ.toFormula.preds ⊆ N := by
    intro κ hκ γ hγ q hq
    apply hN
    simp only [Formula.preds, Formula.atoms, Set.image_union]
    left
    obtain ⟨a, ha, rfl⟩ := hq
    exact ⟨a, atoms_gdisj_sub π κ hκ γ hγ ha, rfl⟩
  unfold toClause at h
  split at h
  · simp only [Option.map_eq_map, Option.map_eq_some_iff] at h
    obtain ⟨f, hf, rfl⟩ := h
    obtain ⟨h1, h2⟩ := filter_spec hR hψ hf
    ext v; simp only [Clause.sem, TrigSem, Set.mem_setOf_eq, h1, h2]
  · rename_i hπ
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨g, hg, f, hf, rfl⟩ := h
    obtain ⟨h1, -⟩ := filter_spec hR hψ hf
    simp only [GDisj.toEGuards, bind, Option.bind_eq_some_iff] at hg
    obtain ⟨κs, hκs, hg⟩ := hg
    have hl := toNList_toList hg
    have hfa := mapM_forall₂ hκs
    have : TrigSem S j π ψ =
        {v | (∃ κ ∈ π, v.dom = κ.toFormula.fv ∧ κ.toFormula.sat S v j) ∧ ψ.sat S v j} := by
      unfold TrigSem; split
      · exact absurd rfl (hπ)
      · rfl
    rw [this]
    ext v
    simp only [Clause.sem, Set.mem_setOf_eq, Option.mem_def, Option.some.injEq, forall_eq',
      forall_eq, h1, hl]
    refine and_congr_left fun _ => ?_
    constructor
    · rintro ⟨κ', hκ', hv⟩
      obtain ⟨κ, hκ, hκκ'⟩ := forall₂_mem_right hfa κ' hκ'
      simp only [bind, Option.bind_eq_some_iff] at hκκ'
      obtain ⟨as, has, hκ'⟩ := hκκ'
      rw [guard_sem hR (hκN κ hκ) has hκ'] at hv
      exact ⟨κ, hκ, hv⟩
    · rintro ⟨κ, hκ, hv⟩
      obtain ⟨κ', hκ', hκκ'⟩ := forall₂_mem_left hfa κ hκ
      simp only [bind, Option.bind_eq_some_iff] at hκκ'
      obtain ⟨as, has, hκ''⟩ := hκκ'
      exact ⟨κ', hκ', by rw [guard_sem hR (hκN κ hκ) has hκ'']; exact hv⟩

end Paper
