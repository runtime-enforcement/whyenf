/-
  `Saturate` on one time-point: sections, fixpoint, provenance.
-/
import Paper.Proof.Point

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem evalList_length {v : Val Voc} : ∀ {ts : List (Term Voc)} {a : List Voc.𝔻},
    Term.evalList v ts = some a → a.length = ts.length
  | [], a, h => by simp [Term.evalList] at h; subst h; rfl
  | t :: ts, a, h => by
    simp only [Term.evalList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨d, -, ds, hds, rfl⟩ := h
    simp [evalList_length hds]

theorem pairwise_of_forall₂ {R : EClause Voc → EClause Voc → Prop} {Q : EClause Voc → Item Voc → Prop}
    {l : List (EClause Voc)} {rules : List (EClause Voc × Item Voc)}
    (h : List.Forall₂ (fun c p => p.1 = c ∧ Q c p.2) l rules) (hp : l.Pairwise R) :
    rules.Pairwise (fun p q => R p.1 q.1) := by
  induction h with
  | nil => exact .nil
  | @cons c p l rules h hs ih =>
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hp
    refine List.Pairwise.cons ?_ (ih h2)
    intro q hq
    obtain ⟨c', hc', hq1⟩ := forall₂_mem_right hs q hq
    rw [h.1, hq1.1]; exact h1 c' hc'

theorem RuleSpec.toClause {c : EClause Voc} {it : Item Voc} (h : RuleSpec c it) :
    ∃ trig, toClause c.π c.ψ = some trig := by
  cases h <;> exact ⟨_, by assumption⟩

namespace Setup
variable (U : Setup Voc)

/-- Two states agree on the events of rank `≤ r`. -/
def AgreeLE (r : ℕ) (y z : Trip Voc) : Prop :=
  ∀ e : REv Voc, U.rk e.1 ≤ r → (e ∈ y.2.1 ↔ e ∈ z.2.1) ∧ (e ∈ y.2.2 ↔ e ∈ z.2.2)

/-- Two states agree on the events of rank `< r`. -/
def AgreeLT (r : ℕ) (y z : Trip Voc) : Prop :=
  ∀ e : REv Voc, U.rk e.1 < r → (e ∈ y.2.1 ↔ e ∈ z.2.1) ∧ (e ∈ y.2.2 ↔ e ∈ z.2.2)

/-- The new events of `z` over `x` have rank at least `r`. -/
def NewGE (r : ℕ) (x z : Trip Voc) : Prop :=
  ∀ e : REv Voc, (e ∈ z.2.1 ∧ e ∉ x.2.1) ∨ (e ∈ z.2.2 ∧ e ∉ x.2.2) → r ≤ U.rk e.1

/-- A rule of a section of rank `r`. -/
structure SecRule (r : ℕ) (p : EClause Voc × Item Voc) : Prop where
  mem : p.1 ∈ U.R
  spec : RuleSpec p.1 p.2
  rank : U.rk p.1.ε.name = r

namespace PtIn
variable {U} (I : U.PtIn) (σ : Trace Voc.toSignature)

theorem Δ_good {c : EClause Voc} (hc : c ∈ U.R) (x : Trip Voc) :
    U.Good (I.Δ (Trace.len σ) c x).2.1 ∧ U.Good (I.Δ (Trace.len σ) c x).2.2 ∧
      (∀ e ∈ (I.Δ (Trace.len σ) c x).2.1, e.1 = c.ε.name) ∧
      (∀ e ∈ (I.Δ (Trace.len σ) c x).2.2, e.1 = c.ε.name) := by
  obtain ⟨⟨hlen, hnl⟩, -⟩ := U.R_props c hc
  have hA : ∀ a ∈ I.A c x, a.length = Voc.ι c.ε.name := by
    rintro a ⟨v, -, hv⟩; rw [evalList_length hv, hlen]
  unfold Δ
  cases hε : c.ε <;> simp only [hε, Effect.name] at hA hnl ⊢
  · refine ⟨fun y hy => ?_, fun y hy => absurd hy (Set.notMem_empty _), fun y hy => hy.1,
      fun y hy => absurd hy (Set.notMem_empty _)⟩
    obtain ⟨h1, h2⟩ := hy; exact ⟨h1 ▸ hA _ h2, h1 ▸ hnl⟩
  · refine ⟨fun y hy => absurd hy (Set.notMem_empty _), fun y hy => ?_,
      fun y hy => absurd hy (Set.notMem_empty _), fun y hy => hy.1⟩
    obtain ⟨h1, h2⟩ := hy; exact ⟨h1 ▸ hA _ h2, h1 ▸ hnl⟩
  all_goals exact ⟨fun y hy => absurd hy (Set.notMem_empty _),
    fun y hy => absurd hy (Set.notMem_empty _), fun y hy => absurd hy (Set.notMem_empty _),
    fun y hy => absurd hy (Set.notMem_empty _)⟩

/-- **Reachable states of a section.** -/
theorem reach_section {r : ℕ} {g : List (EClause Voc × Item Voc)} (hg : ∀ p ∈ g, U.SecRule r p)
    {x y : Trip Voc} (h : ReachS U.P (TablesOf U.L.lets I.H) I.τ I.D σ (g.map Prod.snd) x y)
    (hx : U.Good x.2.1) :
    U.Good y.2.1 ∧ x.le y ∧ U.NewGE r x y ∧
      (∀ e : REv Voc, (e ∈ y.2.1 ∧ e ∉ x.2.1) ∨ (e ∈ y.2.2 ∧ e ∉ x.2.2) → U.rk e.1 = r) ∧
      ∀ (o : Obligation Voc ⊕ (REv Voc ⊕ REv Voc)),
        (match o with
         | .inl o => o ∈ y.1 ∧ o ∉ x.1
         | .inr (.inl e) => e ∈ y.2.1 ∧ e ∉ x.2.1
         | .inr (.inr e) => e ∈ y.2.2 ∧ e ∉ x.2.2) →
        ∃ p ∈ g, ∃ x', ReachS U.P (TablesOf U.L.lets I.H) I.τ I.D σ (g.map Prod.snd) x x' ∧
          x'.le y ∧ U.Good x'.2.1 ∧
          (match o with
           | .inl o => o ∈ (I.Δ (Trace.len σ) p.1 x').1
           | .inr (.inl e) => e ∈ (I.Δ (Trace.len σ) p.1 x').2.1
           | .inr (.inr e) => e ∈ (I.Δ (Trace.len σ) p.1 x').2.2) := by
  induction h with
  | refl =>
    refine ⟨hx, Trip.le_refl _, fun e he => ?_, fun e he => ?_, fun o ho => ?_⟩
    · rcases he with ⟨a, b⟩ | ⟨a, b⟩ <;> exact absurd a b
    · rcases he with ⟨a, b⟩ | ⟨a, b⟩ <;> exact absurd a b
    · rcases o with o | e | e <;> simp at ho
  | @step y it hit hxy ih =>
    obtain ⟨i1, i2, i3, i4, i5⟩ := ih
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hit
    have hsr := hg p hp
    rw [I.upd_rule hsr.spec σ i1]
    obtain ⟨d1, d2, d3, d4⟩ := I.Δ_good σ hsr.mem y
    have hgood : U.Good (y.union (I.Δ (Trace.len σ) p.1 y)).2.1 := by
      rintro e (he | he)
      · exact i1 e he
      · exact d1 e he
    have hrank : ∀ e : REv Voc, (e ∈ (y.union (I.Δ (Trace.len σ) p.1 y)).2.1 ∧ e ∉ x.2.1) ∨
        (e ∈ (y.union (I.Δ (Trace.len σ) p.1 y)).2.2 ∧ e ∉ x.2.2) → U.rk e.1 = r := by
      rintro e (⟨he | he, hn⟩ | ⟨he | he, hn⟩)
      · exact i4 e (Or.inl ⟨he, hn⟩)
      · rw [d3 e he, hsr.rank]
      · exact i4 e (Or.inr ⟨he, hn⟩)
      · rw [d4 e he, hsr.rank]
    refine ⟨hgood, Trip.le_trans i2 (Trip.le_union _ _), fun e he => (hrank e he).ge, hrank,
      fun o ho => ?_⟩
    rcases o with o | e | e
    · simp only [Trip.union, Set.mem_union] at ho
      rcases ho with ⟨ho | ho, hn⟩
      · obtain ⟨p', hp', x', h1, h2, h3, h4⟩ := i5 (.inl o) ⟨ho, hn⟩
        exact ⟨p', hp', x', h1, Trip.le_trans h2 (Trip.le_union _ _), h3, h4⟩
      · exact ⟨p, hp, y, hxy, Trip.le_union _ _, i1, ho⟩
    · simp only [Trip.union, Set.mem_union] at ho
      rcases ho with ⟨ho | ho, hn⟩
      · obtain ⟨p', hp', x', h1, h2, h3, h4⟩ := i5 (.inr (.inl e)) ⟨ho, hn⟩
        exact ⟨p', hp', x', h1, Trip.le_trans h2 (Trip.le_union _ _), h3, h4⟩
      · exact ⟨p, hp, y, hxy, Trip.le_union _ _, i1, ho⟩
    · simp only [Trip.union, Set.mem_union] at ho
      rcases ho with ⟨ho | ho, hn⟩
      · obtain ⟨p', hp', x', h1, h2, h3, h4⟩ := i5 (.inr (.inr e)) ⟨ho, hn⟩
        exact ⟨p', hp', x', h1, Trip.le_trans h2 (Trip.le_union _ _), h3, h4⟩
      · exact ⟨p, hp, y, hxy, Trip.le_union _ _, i1, ho⟩

/-- New elements of any kind. -/
def NewIn (x z : Trip Voc) : Obligation Voc ⊕ (REv Voc ⊕ REv Voc) → Prop
  | .inl o => o ∈ z.1 ∧ o ∉ x.1
  | .inr (.inl e) => e ∈ z.2.1 ∧ e ∉ x.2.1
  | .inr (.inr e) => e ∈ z.2.2 ∧ e ∉ x.2.2

/-- Membership in the additions of a clause. -/
def InΔ (c : EClause Voc) (x : Trip Voc) : Obligation Voc ⊕ (REv Voc ⊕ REv Voc) → Prop
  | .inl o => o ∈ (I.Δ (Trace.len σ) c x).1
  | .inr (.inl e) => e ∈ (I.Δ (Trace.len σ) c x).2.1
  | .inr (.inr e) => e ∈ (I.Δ (Trace.len σ) c x).2.2

theorem NewIn.split {x y z : Trip Voc} (hxy : x.le y) {o : Obligation Voc ⊕ (REv Voc ⊕ REv Voc)}
    (h : NewIn x z o) : NewIn x y o ∨ NewIn y z o := by
  rcases o with o | e | e <;> simp only [NewIn] at h ⊢
  · by_cases hy : o ∈ y.1
    · exact Or.inl ⟨hy, h.2⟩
    · exact Or.inr ⟨h.1, hy⟩
  · by_cases hy : e ∈ y.2.1
    · exact Or.inl ⟨hy, h.2⟩
    · exact Or.inr ⟨h.1, hy⟩
  · by_cases hy : e ∈ y.2.2
    · exact Or.inl ⟨hy, h.2⟩
    · exact Or.inr ⟨h.1, hy⟩

/-- **Running the sections in order of rank.** -/
theorem run_groups : ∀ (gs : List (ℕ × List (EClause Voc × Item Voc))),
    (gs.map Prod.fst).Pairwise (· < ·) → (∀ g ∈ gs, ∀ p ∈ g.2, U.SecRule g.1 p) →
    ∀ x z, RunSecs U.P (TablesOf U.L.lets I.H) I.τ I.D σ (gs.map toSec) x z → U.Good x.2.1 →
      U.Good z.2.1 ∧ x.le z ∧ (∀ r, (∀ g ∈ gs, r ≤ g.1) → U.NewGE r x z) ∧
      (∀ g ∈ gs, ∀ p ∈ g.2, ∃ y, y.le z ∧ U.Good y.2.1 ∧
        upd U.P (TablesOf U.L.lets I.H) I.τ I.D σ p.2 y = y ∧ U.AgreeLE g.1 y z) ∧
      (∀ o, NewIn x z o → ∃ g ∈ gs, ∃ p ∈ g.2, ∃ x', x'.le z ∧ U.Good x'.2.1 ∧
        U.AgreeLT g.1 x' z ∧ I.InΔ σ p.1 x' o)
  | [], _, _, x, z, h, hx => by
    cases h
    refine ⟨hx, Trip.le_refl _, fun r _ e he => ?_, by simp, fun o ho => ?_⟩
    · rcases he with ⟨a, b⟩ | ⟨a, b⟩ <;> exact absurd a b
    · rcases o with o | e | e <;> simp [NewIn] at ho
  | g :: gs, hsort, hg, x, z, h, hx => by
    obtain ⟨hlt, hsort'⟩ := List.pairwise_cons.1 hsort
    cases h with
    | @cons s ss _ y _ hreach hfix hrest =>
      have hrs : (toSec g).2 = g.2.map Prod.snd := rfl
      rw [hrs] at hreach hfix
      obtain ⟨y1, y2, y3, y4, y5⟩ := I.reach_section σ (hg g (by simp)) hreach hx
      obtain ⟨z1, z2, z3, z4, z5⟩ := run_groups gs hsort' (fun g' hg' => hg g' (by simp [hg'])) y z
        hrest y1
      have hnew : ∀ r, (∀ g' ∈ g :: gs, r ≤ g'.1) → U.NewGE r x z := by
        intro r hr e he
        have he' : NewIn x z (.inr (.inl e)) ∨ NewIn x z (.inr (.inr e)) := he
        rcases he' with he' | he' <;> rcases NewIn.split y2 he' with h1 | h1
        · rw [y4 e (Or.inl h1)]; exact hr g (by simp)
        · exact z3 r (fun g' hg' => hr g' (by simp [hg'])) e (Or.inl h1)
        · rw [y4 e (Or.inr h1)]; exact hr g (by simp)
        · exact z3 r (fun g' hg' => hr g' (by simp [hg'])) e (Or.inr h1)
      have hhigh : U.NewGE (g.1 + 1) y z :=
        z3 (g.1 + 1) fun g' hg' => hlt g'.1 (List.mem_map_of_mem hg')
      have hlow : U.NewGE g.1 x z := hnew g.1 fun g' hg' => by
        rcases List.mem_cons.1 hg' with rfl | hg'
        · exact le_rfl
        · exact (hlt g'.1 (List.mem_map_of_mem hg')).le
      refine ⟨z1, Trip.le_trans y2 z2, hnew, fun g' hg' p hp => ?_, fun o ho => ?_⟩
      · rcases List.mem_cons.1 hg' with rfl | hg'
        · refine ⟨y, z2, y1, pass_fix _ _ _ _ _ _ y hfix p.2 (List.mem_map_of_mem hp), fun e he => ?_⟩
          constructor
          · constructor
            · intro h; exact z2.2.1 h
            · intro h; by_contra hn; exact absurd (hhigh e (Or.inl ⟨h, hn⟩)) (by omega)
          · constructor
            · intro h; exact z2.2.2 h
            · intro h; by_contra hn; exact absurd (hhigh e (Or.inr ⟨h, hn⟩)) (by omega)
        · exact z4 g' hg' p hp
      · rcases NewIn.split y2 ho with h1 | h1
        · obtain ⟨p, hp, x', hr', hx'y, hx'g, hΔ⟩ := y5 o h1
          refine ⟨g, by simp, p, hp, x', Trip.le_trans hx'y z2, hx'g, fun e he => ?_, hΔ⟩
          have hxx' := hr'.le
          constructor
          · constructor
            · intro h; exact z2.2.1 (hx'y.2.1 h)
            · intro h; by_contra hn
              have : e ∉ x.2.1 := fun h' => hn (hxx'.2.1 h')
              exact absurd (hlow e (Or.inl ⟨h, this⟩)) (by omega)
          · constructor
            · intro h; exact z2.2.2 (hx'y.2.2 h)
            · intro h; by_contra hn
              have : e ∉ x.2.2 := fun h' => hn (hxx'.2.2 h')
              exact absurd (hlow e (Or.inr ⟨h, this⟩)) (by omega)
        · obtain ⟨g', hg', p, hp, x', h2, h3, h4, h5⟩ := z5 o h1
          exact ⟨g', by simp [hg'], p, hp, x', h2, h3, h4, h5⟩

theorem strOf_agree {y z : Trip Voc} {r : ℕ} (h : U.AgreeLE r y z) :
    (strOf I.H I.τ (REv.toDB (I.Xof y))).Agree (strOf I.H I.τ (REv.toDB (I.Xof z)))
      {e | ¬ IsLet U.L.lets e ∧ U.rk e ≤ r} := by
  refine ⟨rfl, fun j ev hev => ?_⟩
  simp only [strOf]
  split_ifs
  · exact Iff.rfl
  · simp only [REv.toDB, Set.mem_setOf_eq, Xof, Set.mem_union, Set.mem_diff]
    have := h (ev.e, ev.args) hev.2
    rw [this.1, this.2]
  · exact Iff.rfl

theorem A_agree {y z : Trip Voc} {c : EClause Voc} (hc : c ∈ U.R) (hψ : c.ψ.Basic)
    (hy : U.Good y.2.1) (hz : U.Good z.2.1) (h : U.AgreeLE (U.rk c.ε.name) y z) :
    I.A c y = I.A c z := by
  have hA := U.applyLets_agree (I.strOf_agree h) (U.good_noLet (I.good_X hy) I.H I.hH I.τ)
    (U.good_noLet (I.good_X hz) I.H I.hH I.τ)
  have heq : TrigSem (I.St y) I.H.length c.π c.ψ = TrigSem (I.St z) I.H.length c.π c.ψ := by
    refine trigSem_congr hA _ hψ fun q hq e he => ⟨he.base_end, U.trig_rank hc hq he⟩
  simp only [A, heq]

/-- **One time-point of `Saturate`.** -/
theorem saturate_sem (C₀ : Set (REv Voc)) (hC₀ : U.Good C₀) (Ω₀ : Set (Obligation Voc))
    (TN : Tables Voc) {T' : Tables Voc} {C S : Set (REv Voc)} {Ω : Set (Obligation Voc)}
    (h : Saturate U.P ⟨TablesOf U.L.lets I.H, I.τ, I.D, C₀, ∅⟩ TN Ω₀ σ = some (T', C, S, Ω)) :
    U.Good C ∧ Trip.le (Ω₀, C₀, ∅) (Ω, C, S) ∧
      T' = TablesOf U.L.lets (I.H ++ [(I.τ, REv.toDB (I.Xof (Ω, C, S)))]) ∧
      (∀ c ∈ U.R, (I.Δ (Trace.len σ) c (Ω, C, S)).le (Ω, C, S)) ∧
      (∀ o, NewIn (Ω₀, C₀, ∅) (Ω, C, S) o → ∃ c ∈ U.R, ∃ x', x'.le (Ω, C, S) ∧ U.Good x'.2.1 ∧
        U.AgreeLT (U.rk c.ε.name) x' (Ω, C, S) ∧ I.InΔ σ c x' o) := by
  obtain ⟨rules, -, hrules, hsec⟩ := U.prog_spec
  unfold Saturate at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨⟨Ω', C', S'⟩, hrun, hres⟩ := h
  simp only [Prod.mk.injEq] at hres
  obtain ⟨hT', rfl, rfl, rfl⟩ := hres
  set gs := groupByRk U.rk rules
  have hmem : ∀ p ∈ rules, U.SecRule (U.rk p.1.ε.name) p := by
    intro p hp
    obtain ⟨c, hc, rfl, hspec⟩ := forall₂_mem_right hrules p hp
    exact ⟨(U.hrs _).1 (List.mem_mergeSort.1 hc), hspec, rfl⟩
  have hgs : ∀ g ∈ gs, ∀ p ∈ g.2, U.SecRule g.1 p := by
    intro g hg p hp
    have hpr : p ∈ rules := by
      rw [← groupByRk_flatten U.rk rules]; simp only [List.mem_flatten, List.mem_map]
      exact ⟨g.2, ⟨g, hg, rfl⟩, hp⟩
    have := hmem p hpr
    rwa [(groupByRk_rank U.rk rules g hg).2 p hp] at this
  have hsorted : rules.Pairwise (fun p q => U.rk p.1.ε.name ≤ U.rk q.1.ε.name) := by
    have hs := List.pairwise_mergeSort (le := fun c c' => decide (U.rk c.ε.name ≤ U.rk c'.ε.name))
      (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega) U.rs
    have : U.sorted.Pairwise (fun c c' => U.rk c.ε.name ≤ U.rk c'.ε.name) := by
      simpa [sorted] using hs
    exact pairwise_of_forall₂ hrules this
  have hss : ∀ s ∈ U.P.sections, s.1 = .fixpoint := by
    rw [hsec]; intro s hs; obtain ⟨g, -, rfl⟩ := List.mem_map.1 hs; rfl
  have hrs := runSections_spec U.P _ _ _ _ _ hss _ _ hrun
  rw [hsec] at hrs
  obtain ⟨g1, g2, -, g4, g5⟩ := I.run_groups σ gs (groupByRk_sorted U.rk rules hsorted) hgs _ _ hrs hC₀
  refine ⟨g1, g2, ?_, fun c hc => ?_, fun o ho => ?_⟩
  · rw [← hT']
    exact U.tables_final (I.toCtx (Ω', C', S') g1) TN
  · -- the fixpoint
    obtain ⟨p, hp, hpc⟩ := forall₂_mem_left hrules c ((U.hrs c).2 hc |> List.mem_mergeSort.2)
    obtain ⟨rfl, hspec⟩ := hpc
    have hpr : p ∈ rules := hp
    obtain ⟨g, hg, hpg⟩ : ∃ g ∈ gs, p ∈ g.2 := by
      have : p ∈ (gs.map Prod.snd).flatten := by rw [groupByRk_flatten]; exact hpr
      simp only [List.mem_flatten, List.mem_map] at this
      obtain ⟨l, ⟨g, hg, rfl⟩, hl⟩ := this; exact ⟨g, hg, hl⟩
    obtain ⟨y, hyz, hyg, hyfix, hagree⟩ := g4 g hg p hpg
    have hrank : g.1 = U.rk p.1.ε.name := ((groupByRk_rank U.rk rules g hg).2 p hpg).symm
    rw [hrank] at hagree
    obtain ⟨trig, ht⟩ := hspec.toClause
    obtain ⟨f, hf⟩ := toClause_filter ht
    have hA := I.A_agree hc (toFilter_basic hf) hyg g1 hagree
    rw [I.upd_rule hspec σ hyg] at hyfix
    have hle : (I.Δ (Trace.len σ) p.1 y).le y := by
      have := Trip.le_union y (I.Δ (Trace.len σ) p.1 y)
      rw [hyfix] at this
      have h2 : (I.Δ (Trace.len σ) p.1 y).le (y.union (I.Δ (Trace.len σ) p.1 y)) :=
        ⟨Set.subset_union_right, Set.subset_union_right, Set.subset_union_right⟩
      rwa [hyfix] at h2
    have hΔ : I.Δ (Trace.len σ) p.1 y = I.Δ (Trace.len σ) p.1 (Ω', C', S') := by
      simp only [Δ, hA]
    rw [← hΔ]; exact Trip.le_trans hle hyz
  · obtain ⟨g, hg, p, hp, x', h1, h2, h3, h4⟩ := g5 o ho
    have hpr : p ∈ rules := by
      rw [← groupByRk_flatten U.rk rules]; simp only [List.mem_flatten, List.mem_map]
      exact ⟨g.2, ⟨g, hg, rfl⟩, hp⟩
    refine ⟨p.1, (hmem p hpr).mem, x', h1, h2, ?_, h4⟩
    rw [(groupByRk_rank U.rk rules g hg).2 p hp]; exact h3

end PtIn

end Setup

end Paper
