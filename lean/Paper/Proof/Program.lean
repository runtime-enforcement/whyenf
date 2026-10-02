/-
  The shape of `P = Compile(Γ, R, ≺)`: definitions and sections.
-/
import Paper.Proof.Trans

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem sectionsAux_rule {it : Item Voc} (hit : it.isRule) (r : List (Item Voc))
    (cur : Option (SecKind × List (Item Voc))) :
    sectionsAux (it :: r) cur = sectionsAux r (cur.map fun g => (g.1, g.2 ++ [it])) := by
  cases it <;> simp only [Item.isRule, Bool.false_eq_true] at hit
  cases cur <;> rfl

theorem sectionsAux_other {it : Item Voc} (hit : ¬ it.isRule) (hs : ∀ k, it ≠ .sec k)
    (r : List (Item Voc)) (cur : Option (SecKind × List (Item Voc))) :
    sectionsAux (it :: r) cur = sectionsAux r cur := by
  cases it with
  | sec k => exact absurd rfl (hs k)
  | rule => simp [Item.isRule] at hit
  | _ => cases cur <;> rfl

/-- Insert a rule in front of the grouping. -/
def consGroup (rk : Voc.ℰ → ℕ) (p : EClause Voc × Item Voc) :
    List (ℕ × List (EClause Voc × Item Voc)) → List (ℕ × List (EClause Voc × Item Voc))
  | [] => [(rk p.1.ε.name, [p])]
  | (r', g) :: gs =>
    if rk p.1.ε.name = r' then (r', p :: g) :: gs else (rk p.1.ε.name, [p]) :: (r', g) :: gs

/-- Group consecutive rules of equal rank. -/
def groupByRk (rk : Voc.ℰ → ℕ) (l : List (EClause Voc × Item Voc)) :
    List (ℕ × List (EClause Voc × Item Voc)) :=
  l.foldr (consGroup rk) []

/-- A section of the grouped rules. -/
def toSec (g : ℕ × List (EClause Voc × Item Voc)) : SecKind × List (Item Voc) :=
  (.fixpoint, g.2.map Prod.snd)

/-- The sections that `sectionsAux` builds from an open section `(k, acc)` of
    rank `r`, followed by the grouped rules. -/
def secsFrom (r : ℕ) (k : SecKind) (acc : List (Item Voc)) :
    List (ℕ × List (EClause Voc × Item Voc)) → List (SecKind × List (Item Voc))
  | [] => [(k, acc)]
  | (r', g) :: gs =>
    if r' = r then (k, acc ++ g.map Prod.snd) :: gs.map toSec
    else (k, acc) :: ((r', g) :: gs).map toSec

theorem secsFrom_cons (rk : Voc.ℰ → ℕ) (p : EClause Voc × Item Voc) (gs) (r : ℕ) (k : SecKind)
    (acc : List (Item Voc)) (hr : rk p.1.ε.name = r) :
    secsFrom r k (acc ++ [p.2]) gs = secsFrom r k acc (consGroup rk p gs) := by
  cases gs with
  | nil => simp [secsFrom, consGroup, hr]
  | cons x gs =>
    obtain ⟨r', g⟩ := x
    by_cases hr' : r' = r
    · subst hr'; simp [secsFrom, consGroup, hr]
    · simp [secsFrom, consGroup, hr, hr', Ne.symm hr', toSec]

theorem secsFrom_new (rk : Voc.ℰ → ℕ) (p : EClause Voc × Item Voc) (gs) (r : ℕ) (k : SecKind)
    (acc : List (Item Voc)) (hr : rk p.1.ε.name ≠ r) :
    (k, acc) :: secsFrom (rk p.1.ε.name) .fixpoint [p.2] gs =
      secsFrom r k acc (consGroup rk p gs) := by
  cases gs with
  | nil => simp [secsFrom, consGroup, hr, toSec]
  | cons x gs =>
    obtain ⟨r', g⟩ := x
    by_cases hr' : rk p.1.ε.name = r'
    · subst hr'; simp [secsFrom, consGroup, hr, toSec]
    · simp [secsFrom, consGroup, hr, hr', Ne.symm hr', toSec]

theorem sections_withSections_aux (rk : Voc.ℰ → ℕ) :
    ∀ (l : List (EClause Voc × Item Voc)), (∀ p ∈ l, p.2.isRule) →
      ∀ (r : ℕ) (k : SecKind) (acc : List (Item Voc)),
        sectionsAux (withSections rk (some r) l) (some (k, acc)) = secsFrom r k acc (groupByRk rk l)
  | [], _, r, k, acc => by simp [withSections, sectionsAux, groupByRk, secsFrom]
  | p :: rest, hl, r, k, acc => by
    have hit : p.2.isRule := hl p (by simp)
    have hrest : ∀ p ∈ rest, p.2.isRule := fun p hp => hl p (by simp [hp])
    obtain ⟨c, it⟩ := p
    simp only [groupByRk, List.foldr_cons]
    rw [← groupByRk]
    by_cases hr : rk c.ε.name = r
    · have hw : withSections rk (some r) ((c, it) :: rest) = it :: withSections rk (some r) rest := by
        simp [withSections, hr]
      rw [hw, sectionsAux_rule hit, Option.map_some, sections_withSections_aux rk rest hrest r k]
      exact secsFrom_cons rk (c, it) _ r k acc hr
    · have hw : withSections rk (some r) ((c, it) :: rest) =
          .sec .fixpoint :: it :: withSections rk (some (rk c.ε.name)) rest := by
        simp [withSections, Ne.symm hr, hr]
      rw [hw, show sectionsAux (.sec .fixpoint :: it :: withSections rk (some (rk c.ε.name)) rest)
          (some (k, acc)) = (k, acc) :: sectionsAux (it :: withSections rk (some (rk c.ε.name)) rest)
            (some (.fixpoint, [])) from rfl,
        sectionsAux_rule hit, Option.map_some, sections_withSections_aux rk rest hrest]
      exact secsFrom_new rk (c, it) _ r k acc hr

theorem sections_withSections (rk : Voc.ℰ → ℕ) (l : List (EClause Voc × Item Voc))
    (hl : ∀ p ∈ l, p.2.isRule) :
    sectionsAux (withSections rk none l) none = (groupByRk rk l).map toSec := by
  cases l with
  | nil => simp [withSections, sectionsAux, groupByRk]
  | cons p rest =>
    have hit : p.2.isRule := hl p (by simp)
    have hrest : ∀ p ∈ rest, p.2.isRule := fun p hp => hl p (by simp [hp])
    obtain ⟨c, it⟩ := p
    have hw : withSections rk none ((c, it) :: rest) =
        .sec .fixpoint :: it :: withSections rk (some (rk c.ε.name)) rest := by
      simp [withSections]
    rw [hw, show sectionsAux (.sec .fixpoint :: it :: withSections rk (some (rk c.ε.name)) rest) none =
        sectionsAux (it :: withSections rk (some (rk c.ε.name)) rest) (some (.fixpoint, [])) from rfl,
      sectionsAux_rule hit, Option.map_some, sections_withSections_aux rk rest hrest]
    simp only [groupByRk, List.foldr_cons]
    rw [← groupByRk]
    cases hg : groupByRk rk rest with
    | nil => simp [secsFrom, consGroup, toSec]
    | cons x gs =>
      obtain ⟨r', g⟩ := x
      by_cases hr' : rk c.ε.name = r'
      · subst hr'; simp [secsFrom, consGroup, toSec]
      · simp [secsFrom, consGroup, hr', Ne.symm hr', toSec]

theorem sectionsAux_skip :
    ∀ (its : List (Item Voc)) (ws : List (Item Voc)), (∀ it ∈ its, ¬ it.isRule ∧ ∀ k, it ≠ .sec k) →
      sectionsAux (its ++ ws) none = sectionsAux ws none
  | [], ws, _ => rfl
  | it :: its, ws, h => by
    obtain ⟨h1, h2⟩ := h it (by simp)
    rw [List.cons_append, sectionsAux_other h1 h2]
    exact sectionsAux_skip its ws fun i hi => h i (by simp [hi])

/-! ### Properties of the grouping -/

theorem consGroup_flatten (rk : Voc.ℰ → ℕ) (p : EClause Voc × Item Voc) (gs) :
    ((consGroup rk p gs).map Prod.snd).flatten = p :: (gs.map Prod.snd).flatten := by
  cases gs with
  | nil => simp [consGroup]
  | cons x gs => obtain ⟨r', g⟩ := x; simp only [consGroup]; split_ifs <;> simp

theorem groupByRk_flatten (rk : Voc.ℰ → ℕ) :
    ∀ l : List (EClause Voc × Item Voc), ((groupByRk rk l).map Prod.snd).flatten = l
  | [] => rfl
  | p :: rest => by
    simp only [groupByRk, List.foldr_cons]; rw [← groupByRk, consGroup_flatten, groupByRk_flatten rk rest]

theorem groupByRk_rank (rk : Voc.ℰ → ℕ) :
    ∀ l : List (EClause Voc × Item Voc), ∀ x ∈ groupByRk rk l,
      x.2 ≠ [] ∧ ∀ p ∈ x.2, rk p.1.ε.name = x.1
  | [] => by simp [groupByRk]
  | p :: rest => by
    have ih := groupByRk_rank rk rest
    simp only [groupByRk, List.foldr_cons]; rw [← groupByRk]
    cases hg : groupByRk rk rest with
    | nil =>
      simp only [consGroup]; intro y hy
      simp only [List.mem_singleton] at hy; subst hy
      exact ⟨by simp, by simp⟩
    | cons x gs =>
      obtain ⟨r', g⟩ := x
      rw [hg] at ih
      simp only [consGroup]
      split_ifs with h
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · refine ⟨by simp, ?_⟩
          intro q hq
          rcases List.mem_cons.1 hq with rfl | hq
          · exact h
          · exact (ih (r', g) (by simp)).2 q hq
        · exact ih y (by simp [hy])
      · intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · simp
        · exact ih y hy

/-- On a list sorted by rank, the groups have strictly increasing ranks. -/
theorem groupByRk_sorted (rk : Voc.ℰ → ℕ) :
    ∀ l : List (EClause Voc × Item Voc), l.Pairwise (fun p q => rk p.1.ε.name ≤ rk q.1.ε.name) →
      ((groupByRk rk l).map Prod.fst).Pairwise (· < ·)
  | [], _ => by simp [groupByRk]
  | p :: rest, h => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    have ih := groupByRk_sorted rk rest h2
    have hall : ∀ x ∈ groupByRk rk rest, rk p.1.ε.name ≤ x.1 := by
      intro x hx
      obtain ⟨hne, hrk⟩ := groupByRk_rank rk rest x hx
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
      have hql : q ∈ rest := by
        rw [← groupByRk_flatten rk rest]; simp only [List.mem_flatten, List.mem_map]
        exact ⟨x.2, ⟨x, hx, rfl⟩, hq⟩
      rw [← hrk q hq]; exact h1 q hql
    simp only [groupByRk, List.foldr_cons]; rw [← groupByRk]
    cases hg : groupByRk rk rest with
    | nil => simp [consGroup]
    | cons x gs =>
      obtain ⟨r', g⟩ := x
      rw [hg] at ih hall
      simp only [consGroup]
      split_ifs with he
      · simpa using ih
      · simp only [List.map_cons, List.pairwise_cons] at ih ⊢
        refine ⟨?_, ih⟩
        intro a ha
        rcases List.mem_cons.1 ha with hEq | ha
        · rw [hEq]; exact lt_of_le_of_ne (hall (r', g) (by simp)) he
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
          exact lt_of_le_of_lt (hall (r', g) (by simp)) (ih.1 _ (List.mem_map_of_mem hy))

end Paper
