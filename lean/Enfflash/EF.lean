/-
  EnfFlash formalization — EF programs (paper, Section 3): syntax (guards,
  triggers, effects, rules/clauses, sections) and semantics (rule firing,
  `Saturate`, tables, and the enforcement loop).
-/
import Enfflash.MFOTL

namespace Enfflash

universe u
variable {B L D : Type u}

/-! ## Guards -/

/-- A guard atom: a predicate over terms, or an equation `t == d`. -/
inductive GAtom (B L D : Type u) where
  | pred : Pr B L → List (Term D) → GAtom B L D
  | eq : Term D → D → GAtom B L D

namespace GAtom

def sat (σ : Tr B L D) (i : ℕ) (v : ℕ → D) : GAtom B L D → Prop
  | pred p ts => σ.prIn i p (ts.map (Term.eval v))
  | eq t d => t.eval v = d

def toFm : GAtom B L D → Fm B L D
  | pred p ts => .pred p ts
  | eq t d => .eq t (.const d)

theorem sat_toFm (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (a : GAtom B L D) :
    σ.sat i v a.toFm ↔ a.sat σ i v := by
  cases a <;> rfl

/-- `a` binds variable `x`: `x` occurs as a plain argument. -/
def binds (x : ℕ) : GAtom B L D → Prop
  | pred _ ts => Term.var x ∈ ts
  | eq t _ => t = Term.var x

def subst (s : ℕ → Term D) : GAtom B L D → GAtom B L D
  | pred p ts => pred p (ts.map (Term.subst s))
  | eq t d => eq (t.subst s) d

theorem sat_subst (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (s : ℕ → Term D)
    (a : GAtom B L D) : (a.subst s).sat σ i v ↔ a.sat σ i (fun n => (s n).eval v) := by
  cases a with
  | pred p ts =>
    simp only [subst, sat, List.map_map]
    have : (Term.eval v ∘ Term.subst s) = Term.eval (fun n => (s n).eval v) := by
      funext t; simp
    rw [this]
  | eq t d => simp [subst, sat]

end GAtom

/-- A disjunction of conjunctions of guard atoms. -/
abbrev Guards (B L D : Type u) := List (List (GAtom B L D))

namespace Guards

def sat (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (π : Guards B L D) : Prop :=
  ∃ κ ∈ π, ∀ a ∈ κ, a.sat σ i v

/-- The trivial guard `⊤` (one empty conjunction). -/
def top : Guards B L D := [[]]

@[simp] theorem sat_top (σ : Tr B L D) (i : ℕ) (v : ℕ → D) :
    Guards.sat σ i v (top : Guards B L D) := ⟨[], by simp [top], by simp⟩

@[simp] theorem sat_append (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (π π' : Guards B L D) :
    sat σ i v (π ++ π') ↔ sat σ i v π ∨ sat σ i v π' := by
  simp [sat, or_and_right, exists_or]

/-- Conjoin one atom to every disjunct. -/
def addAtom (π : Guards B L D) (a : GAtom B L D) : Guards B L D := π.map (· ++ [a])

theorem sat_addAtom (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (π : Guards B L D)
    (a : GAtom B L D) : sat σ i v (addAtom π a) ↔ sat σ i v π ∧ a.sat σ i v := by
  constructor
  · rintro ⟨κ', hκ', h⟩
    obtain ⟨κ, hκ, rfl⟩ := List.mem_map.1 hκ'
    exact ⟨⟨κ, hκ, fun b hb => h b (List.mem_append_left _ hb)⟩, h a (by simp)⟩
  · rintro ⟨⟨κ, hκ, h⟩, ha⟩
    refine ⟨κ ++ [a], List.mem_map.2 ⟨κ, hκ, rfl⟩, fun b hb => ?_⟩
    rcases List.mem_append.1 hb with hb | hb
    · exact h b hb
    · rw [List.mem_singleton.1 hb]; exact ha

def subst (s : ℕ → Term D) (π : Guards B L D) : Guards B L D :=
  π.map (List.map (GAtom.subst s))

theorem sat_subst (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (s : ℕ → Term D)
    (π : Guards B L D) : sat σ i v (π.subst s) ↔ sat σ i (fun n => (s n).eval v) π := by
  simp [sat, subst, GAtom.sat_subst]

def conjFm (κ : List (GAtom B L D)) : Fm B L D := κ.foldr (fun a f => Fm.conj a.toFm f) .tt

/-- The guards as a formula (used when guards move into a filter). -/
def toFm : Guards B L D → Fm B L D
  | [] => .neg .tt
  | κ :: π => Fm.disj (conjFm κ) (toFm π)

theorem sat_conjFm (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (κ : List (GAtom B L D)) :
    σ.sat i v (conjFm κ) ↔ ∀ a ∈ κ, a.sat σ i v := by
  induction κ with
  | nil => simp [conjFm, Tr.sat]
  | cons a κ ih =>
    simp only [conjFm, List.foldr_cons] at ih ⊢
    simp [Tr.sat, ih, GAtom.sat_toFm]

theorem sat_toFm (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (π : Guards B L D) :
    σ.sat i v π.toFm ↔ sat σ i v π := by
  induction π with
  | nil => simp [toFm, sat, Tr.sat]
  | cons κ π ih => rw [toFm, Tr.sat_disj, sat_conjFm, ih]; simp [sat]

/-- Every disjunct binds `x`. -/
def bindsAll (x : ℕ) (π : Guards B L D) : Prop := ∀ κ ∈ π, ∃ a ∈ κ, a.binds x

end Guards

/-! ## Triggers, effects, clauses -/

structure Trigger (B L D : Type u) where
  guards : Guards B L D
  filter : Fm B L D

namespace Trigger

def sat (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (θ : Trigger B L D) : Prop :=
  θ.guards.sat σ i v ∧ σ.sat i v θ.filter

def top : Trigger B L D := ⟨Guards.top, .tt⟩

def subst (s : ℕ → Term D) (θ : Trigger B L D) : Trigger B L D :=
  ⟨θ.guards.subst s, θ.filter.subst s⟩

theorem sat_subst (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (s : ℕ → Term D)
    (θ : Trigger B L D) : (θ.subst s).sat σ i v ↔ θ.sat σ i (fun n => (s n).eval v) := by
  simp [sat, subst, Guards.sat_subst, Tr.sat_subst]

/-- Conjoin an extra condition to the filter. -/
def andFilter (θ : Trigger B L D) (φ : Fm B L D) : Trigger B L D :=
  ⟨θ.guards, .conj θ.filter φ⟩

end Trigger

/-- Effects of a clause.  `later b` is a proactive causation `b` time units
    later (EF's `[delay b]`, from `◇_[a,b]`); `next n t` is a causation `n`
    time-points later (EF's `[next n]`, from `○ … ○`); if `t` is set, the next
    time-point must moreover be at most one time unit later (single bounded
    `○_[0,b]`, `b ≥ 1`). -/
inductive Effect (B L D : Type u) where
  | cau : Ev B L → List (Term D) → Effect B L D
  | sup : Ev B L → List (Term D) → Effect B L D
  | later : ℕ → Ev B L → List (Term D) → Effect B L D
  | next : ℕ → Bool → Ev B L → List (Term D) → Effect B L D

namespace Effect

def args : Effect B L D → List (Term D)
  | cau _ ts | sup _ ts | later _ _ ts | next _ _ _ ts => ts

def name : Effect B L D → Ev B L
  | cau e _ | sup e _ | later _ e _ | next _ _ e _ => e

def subst (s : ℕ → Term D) : Effect B L D → Effect B L D
  | cau e ts => cau e (ts.map (Term.subst s))
  | sup e ts => sup e (ts.map (Term.subst s))
  | later b e ts => later b e (ts.map (Term.subst s))
  | next n t e ts => next n t e (ts.map (Term.subst s))

/-- `j` is the last time-point with timestamp `t` (where the proactive
    function `ν` inserts events for timestamp `t`). -/
def lastAt (σ : Tr B L D) (t j : ℕ) : Prop := σ.ts j = t ∧ t < σ.ts (j + 1)

/-- The meaning of an effect at time-point `i` of an (output) trace. -/
def holds (σ : Tr B L D) (i : ℕ) (v : ℕ → D) : Effect B L D → Prop
  | cau e ts => (e, ts.map (Term.eval v)) ∈ σ.db i
  | sup e ts => (e, ts.map (Term.eval v)) ∉ σ.db i
  | later b e ts => ∃ j, lastAt σ (σ.ts i + b) j ∧ (e, ts.map (Term.eval v)) ∈ σ.db j
  | next n t e ts => (t = true → σ.ts (i + 1) ≤ σ.ts i + 1) ∧
      (e, ts.map (Term.eval v)) ∈ σ.db (i + n)

theorem holds_subst (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (s : ℕ → Term D)
    (ε : Effect B L D) : (ε.subst s).holds σ i v ↔ ε.holds σ i (fun n => (s n).eval v) := by
  have h : ∀ ts : List (Term D), (ts.map (Term.subst s)).map (Term.eval v) =
      ts.map (Term.eval (fun n => (s n).eval v)) := by
    intro ts; simp [List.map_map, Function.comp_def]
  cases ε <;> simp only [subst, holds, h]

end Effect

/-- A clause `θ ⇒ ε` under `nloc` universally quantified local variables
    (de Bruijn indices `0 … nloc-1`); indices `≥ nloc` refer to the context. -/
structure Clause (B L D : Type u) where
  nloc : ℕ
  trig : Trigger B L D
  eff : Effect B L D

namespace Clause

/-- The clause holds at time-point `i` of `σ` in context `v`. -/
def holds (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (c : Clause B L D) : Prop :=
  ∀ ds : List D, ds.length = c.nloc → c.trig.sat σ i (vapp ds v) → c.eff.holds σ i (vapp ds v)

/-- Substitution acting on the *context* variables of a clause. -/
def substCtx (s : ℕ → Term D) (c : Clause B L D) : Clause B L D :=
  let s' : ℕ → Term D := fun n => if n < c.nloc then .var n else (s (n - c.nloc)).subst (liftS c.nloc)
  ⟨c.nloc, c.trig.subst s', c.eff.subst s'⟩

theorem holds_substCtx (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (s : ℕ → Term D)
    (c : Clause B L D) : (c.substCtx s).holds σ i v ↔ c.holds σ i (fun n => (s n).eval v) := by
  have key : ∀ ds : List D, ds.length = c.nloc →
      (fun n => (if n < c.nloc then Term.var n else (s (n - c.nloc)).subst (liftS c.nloc)).eval
        (vapp ds v)) = vapp ds (fun n => (s n).eval v) := by
    intro ds hds; funext n
    split_ifs with h
    · simp [Term.eval, vapp_lt _ _ _ (hds ▸ h)]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + c.nloc := ⟨n - c.nloc, by omega⟩
      rw [Term.eval_subst, ← hds, eval_liftS, hds, show m + c.nloc - c.nloc = m by omega,
        ← hds, vapp_ge]
  simp only [holds, substCtx, Trigger.sat_subst, Effect.holds_subst]
  constructor
  · intro h ds hds; rw [← key ds hds]; exact h ds hds
  · intro h ds hds; rw [key ds hds]; exact h ds hds

end Clause

/-- A set of clauses holds. -/
def Clauses.holds (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (C : List (Clause B L D)) : Prop :=
  ∀ c ∈ C, c.holds σ i v

/-! ## Operational semantics of one time-point (Algorithm 2) -/

/-- Ground instances of effects ("actions"): elements of `C`, `S` and `Ω`. -/
inductive Act (B L D : Type u) where
  | cau : Ev B L × List D → Act B L D
  | sup : Ev B L × List D → Act B L D
  | later : ℕ → Ev B L × List D → Act B L D
  | next : ℕ → Bool → Ev B L × List D → Act B L D

def Act.name : Act B L D → Ev B L
  | cau x | sup x | later _ x | next _ _ x => x.1

def Effect.act (w : ℕ → D) : Effect B L D → Act B L D
  | .cau e ts => .cau (e, ts.map (Term.eval w))
  | .sup e ts => .sup (e, ts.map (Term.eval w))
  | .later b e ts => .later b (e, ts.map (Term.eval w))
  | .next n t e ts => .next n t (e, ts.map (Term.eval w))

theorem Effect.act_name (w : ℕ → D) (ε : Effect B L D) : (ε.act w).name = ε.name := by
  cases ε <;> rfl

/-- The working set `(D ∖ S) ∪ C`. -/
def work (D₀ : DB B L D) (X : Set (Act B L D)) : DB B L D :=
  {x | (x ∈ D₀ ∧ Act.sup x ∉ X) ∨ Act.cau x ∈ X}

/-- Evaluation context of one time-point: the interpretation of tables and
    lets as a function of the working set (`R_i` in the paper), and the
    context valuation. -/
structure Ctx (B L D : Type u) where
  lv : DB B L D → L → List D → Prop
  v₀ : ℕ → D

/-- A single-point trace used to evaluate (present) triggers on a working set. -/
def ptTr (W : DB B L D) (lv : L → List D → Prop) : Tr B L D :=
  ⟨fun _ => W, fun _ => 0, fun _ => lv⟩

/-- Rule `c` fires on working set `W`, producing action `a` (`𝒜_S(r)`). -/
def fires (K : Ctx B L D) (W : DB B L D) (c : Clause B L D) (a : Act B L D) : Prop :=
  ∃ ds : List D, ds.length = c.nloc ∧ c.trig.sat (ptTr W (K.lv W)) 0 (vapp ds K.v₀) ∧
    a = c.eff.act (vapp ds K.v₀)

/-- `Update` (Algorithm 2) for a single rule `c`: add all actions of its
    matches on the current working set. -/
def update (K : Ctx B L D) (D₀ : DB B L D) (c : Clause B L D)
    (X : Set (Act B L D)) : Set (Act B L D) :=
  X ∪ {a | fires K (work D₀ X) c a}

/-- One pass of the `repeat` loop of `Saturate` (Algorithm 2): `Update` for
    every rule of the section, in order, each on the working set left by the
    previous ones. -/
def step (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D))
    (X : Set (Act B L D)) : Set (Act B L D) :=
  sec.foldl (fun Y c => update K D₀ c Y) X

/-- `X` is a fixpoint of the section. -/
def Fixed (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D))
    (X : Set (Act B L D)) : Prop :=
  ∀ c ∈ sec, ∀ a, fires K (work D₀ X) c a → a ∈ X

/-- Induction principle for a pass. -/
theorem step_induct (K : Ctx B L D) (D₀ : DB B L D) (P : Set (Act B L D) → Prop) :
    ∀ (sec : List (Clause B L D)), (∀ c ∈ sec, ∀ Y, P Y → P (update K D₀ c Y)) →
      ∀ X, P X → P (step K D₀ sec X)
  | [], _, _, hX => hX
  | c :: cs, h, X, hX =>
    step_induct K D₀ P cs (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')) _
      (h c (List.mem_cons_self ..) X hX)

theorem subset_step (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D))
    (X : Set (Act B L D)) : X ⊆ step K D₀ sec X :=
  step_induct K D₀ (X ⊆ ·) sec (fun _ _ _ h => h.trans Set.subset_union_left) X le_rfl

/-- Every rule of a pass is applied to an intermediate working set. -/
theorem step_rule (K : Ctx B L D) (D₀ : DB B L D) :
    ∀ (sec : List (Clause B L D)) (X : Set (Act B L D)), ∀ c ∈ sec, ∃ Z,
      X ⊆ Z ∧ Z ⊆ step K D₀ sec X ∧ update K D₀ c Z ⊆ step K D₀ sec X
  | [], _, c, hc => absurd hc (List.not_mem_nil)
  | c' :: cs, X, c, hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨X, le_rfl, Set.subset_union_left.trans (subset_step K D₀ cs _),
        subset_step K D₀ cs _⟩
    · obtain ⟨Z, h1, h2, h3⟩ := step_rule K D₀ cs (update K D₀ c' X) c hc
      exact ⟨Z, Set.subset_union_left.trans h1, h2, h3⟩

/-- Every new action of a pass is produced by a rule of the section on an
    intermediate working set. -/
theorem step_cases (K : Ctx B L D) (D₀ : DB B L D) :
    ∀ (sec : List (Clause B L D)) (X : Set (Act B L D)), ∀ a ∈ step K D₀ sec X,
      a ∈ X ∨ ∃ Z, X ⊆ Z ∧ Z ⊆ step K D₀ sec X ∧ ∃ c ∈ sec, fires K (work D₀ Z) c a
  | [], _, _, ha => Or.inl ha
  | c :: cs, X, a, ha => by
    rcases step_cases K D₀ cs (update K D₀ c X) a ha with (h | h) | ⟨Z, h1, h2, c', hc', hf⟩
    · exact Or.inl h
    · exact Or.inr ⟨X, le_rfl, Set.subset_union_left.trans (subset_step K D₀ cs _),
        c, List.mem_cons_self .., h⟩
    · exact Or.inr ⟨Z, Set.subset_union_left.trans h1, h2, c', List.mem_cons_of_mem _ hc', hf⟩

/-- `Saturate` stops a `fixpoint` section when a pass leaves `(Ω, C, S)`
    unchanged, i.e., exactly at a fixpoint. -/
theorem step_eq_iff_fixed (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D))
    (X : Set (Act B L D)) : step K D₀ sec X = X ↔ Fixed K D₀ sec X := by
  constructor
  · intro h c hc a ha
    obtain ⟨Z, h1, h2, h3⟩ := step_rule K D₀ sec X c hc
    rw [h] at h2 h3
    have hZ : Z = X := Set.Subset.antisymm h2 h1
    subst hZ
    exact h3 (Or.inr ha)
  · intro h
    refine step_induct K D₀ (· = X) sec (fun c hc Y hY => ?_) X rfl
    subst hY
    exact Set.Subset.antisymm (Set.union_subset le_rfl fun a ha => h c hc a ha)
      Set.subset_union_left

/-- Running the sections in order: each section is iterated (`n` passes) until
    it reaches a fixpoint.  (A `once` section is the case `n = 1`, whose
    fixpoint property follows from `once_fixed`.) -/
inductive SatRun (K : Ctx B L D) (D₀ : DB B L D) :
    List (List (Clause B L D)) → Set (Act B L D) → Set (Act B L D) → Prop
  | nil {X} : SatRun K D₀ [] X X
  | cons {sec secs X Y Z} (n : ℕ) : Y = (step K D₀ sec)^[n] X → Fixed K D₀ sec Y →
      SatRun K D₀ secs Y Z → SatRun K D₀ (sec :: secs) X Z

/-- The trigger of `c` only depends on events whose names are in `N`
    (tables and lets being accounted for through the events defining them,
    as in the EDG). -/
def TrigDeps (K : Ctx B L D) (c : Clause B L D) (N : Set (Ev B L)) : Prop :=
  ∀ W W' : DB B L D, (∀ e ∈ N, ∀ as, (e, as) ∈ W ↔ (e, as) ∈ W') →
    ∀ w, c.trig.sat (ptTr W (K.lv W)) 0 w ↔ c.trig.sat (ptTr W' (K.lv W')) 0 w

/-- No event is both caused and suppressed. -/
def ConflictFree (X : Set (Act B L D)) : Prop := ∀ x, ¬ (Act.cau x ∈ X ∧ Act.sup x ∈ X)

/-! ## Tables -/

section
variable (σ : Tr B L D) (v₀ : ℕ → D)

/-- Rows `(τ', ā)` of a since table after time-point `i`: rows are removed
    when the left operand fails and inserted (with the current timestamp)
    when the right operand holds (Algorithm 2, table update in `Saturate`). -/
def sinceStore (φl φr : Fm B L D) : ℕ → Set (ℕ × List D)
  | 0 => {r | r.1 = σ.ts 0 ∧ σ.sat 0 (vapp r.2 v₀) φr}
  | i + 1 => {r | r ∈ sinceStore φl φr i ∧ σ.sat (i + 1) (vapp r.2 v₀) φl} ∪
      {r | r.1 = σ.ts (i + 1) ∧ σ.sat (i + 1) (vapp r.2 v₀) φr}

/-- The value of a windowed table: rows inserted between `a` and `b` time
    units ago (the paper's `𝒲`). -/
def sinceVal (a : ℕ) (b : Option ℕ) (φl φr : Fm B L D) (i : ℕ) (as : List D) : Prop :=
  ∃ τ', (τ', as) ∈ sinceStore σ v₀ φl φr i ∧ inI a b (σ.ts i - τ')

/-- A lagged table holds the rows inserted at the previous time-point. -/
def prevVal (a : ℕ) (b : Option ℕ) (φ : Fm B L D) : ℕ → List D → Prop
  | 0, _ => False
  | i + 1, as => ∃ τ', (τ' = σ.ts i ∧ σ.sat i (vapp as v₀) φ) ∧ inI a b (σ.ts (i + 1) - τ')

end

/-! ## Programs and the enforcement loop (Algorithm 1) -/

/-- An EF program: its rules, grouped into sections (in EDG order). -/
structure Program (B L D : Type u) where
  secs : List (List (Clause B L D))

def Program.rules (P : Program B L D) : List (Clause B L D) := P.secs.flatten

/-- A run of the enforcement loop producing output trace `σ`. -/
structure LoopRun (P : Program B L D) (σ : Tr B L D) (v₀ : ℕ → D) where
  /-- evaluation context (tables/lets as a function of the working set) -/
  K : ℕ → Ctx B L D
  /-- input database (`D_k` for reactive time-points, `∅` for proactive ones) -/
  D₀ : ℕ → DB B L D
  /-- obligations due at this time-point -/
  init : ℕ → Set (Act B L D)
  /-- final `(C, S, Ω)` of `Saturate` -/
  X : ℕ → Set (Act B L D)
  hv₀ : ∀ j, (K j).v₀ = v₀
  run : ∀ j, SatRun (K j) (D₀ j) P.secs (init j) (X j)
  db : ∀ j, σ.db j = work (D₀ j) (X j)
  lv : ∀ j, σ.lv j = (K j).lv (σ.db j)
  laterFire : ∀ i b x, Act.later b x ∈ X i →
    ∃ j, Effect.lastAt σ (σ.ts i + b) j ∧ Act.cau x ∈ init j
  nextFire : ∀ i n t x, Act.next n t x ∈ X i →
    (t = true → σ.ts (i + 1) ≤ σ.ts i + 1) ∧ Act.cau x ∈ init (i + n)
  /-- the initial actions are exactly causations of due obligations -/
  initSrc : ∀ j a, a ∈ init j → ∃ x, a = Act.cau x ∧
    ∃ i, (∃ b, Act.later b x ∈ X i) ∨ (∃ n t, Act.next n t x ∈ X i)

end Enfflash
