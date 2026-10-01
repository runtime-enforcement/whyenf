/-
  EnfFlash formalization — soundness of the cause/suppress conflict check
  (paper, Section 4.5, "Cause/suppress conflicts"; `src/smt_check.ml`).

  During a fixpoint, `C` and `S` only grow: a rule that fired in an early
  iteration keeps its effect even if its trigger no longer holds later.  The
  check therefore has to exclude that a cause and a suppression of the same
  instance fire on *different* working sets of the run.  Two working sets of
  the same section agree on all events not acted upon by the section (in
  particular, on events of strictly upstream SCCs), but may differ on the
  others.  This is what `ExclusiveNow` expresses, and what the SMT check
  establishes by sharing only upstream events between the two triggers
  (`smt_check.ml` gives all other atoms side-private symbols).

  Deferred effects (`[delay]`/`[next]`) are discharged at a later time-point,
  where even upstream events may differ: `ExclusiveDeferred` requires the two
  triggers to be exclusive without sharing anything.  (The original
  implementation shared upstream events for such pairs too, which is unsound;
  fixed in `smt_check.ml`.)

  The check itself is stated on the EDG (`ConflictCheck`): every
  cause/suppress pair of an event yields a conflict query that a sound SMT
  solver reports unsatisfiable.  `ConflictCheck.exclusive` proves that it
  establishes `Exclusive`.
-/
import Enfflash.EDG
import Enfflash.Enforcer

namespace Enfflash

universe u
variable {B L D : Type u}

/-- Events acted upon by the rules of a section. -/
def effNames (sec : List (Clause B L D)) : Set (Ev B L) := {e | ∃ c ∈ sec, c.eff.name = e}

/-- What the SMT check establishes for rules `c₁`, `c₂` of one section: no
    instance is caused by `c₁` and suppressed by `c₂` on working sets that
    agree on the events in `F` (those not acted upon by the section). -/
def ExclusiveNow (K : Ctx B L D) (F : Set (Ev B L)) (c₁ c₂ : Clause B L D) : Prop :=
  ∀ W₁ W₂ : DB B L D, (∀ e ∈ F, ∀ as, (e, as) ∈ W₁ ↔ (e, as) ∈ W₂) →
    ∀ x, fires K W₁ c₁ (.cau x) → ¬ fires K W₂ c₂ (.sup x)

/-- The instance that a deferred action causes. -/
def Act.deferred : Act B L D → Option (Ev B L × List D)
  | later _ x | next _ _ x => some x
  | _ => none

/-- Exclusivity of a deferred cause (fired at some time-point) and a
    suppression (fired at a later time-point): nothing is shared. -/
def ExclusiveDeferred (c₁ c₂ : Clause B L D) : Prop :=
  ∀ (K₁ K₂ : Ctx B L D) (W₁ W₂ : DB B L D) a x, fires K₁ W₁ c₁ a → a.deferred = some x →
    ¬ fires K₂ W₂ c₂ (.sup x)

/-- **The conflict check** (paper, Section 4.5) for a rule `c₁` of a section
    and a rule `c₂`: an instance caused by `c₁` is never suppressed by `c₂`.
    For an immediate cause, the two triggers are evaluated at the same
    time-point: they share the context `K` and the events `F` not acted upon by
    the section (`ExclusiveNow`).  For a deferred cause (`[delay]`/`[next]`),
    the suppression happens at a later time-point, and nothing is shared
    (`ExclusiveDeferred`). -/
def Exclusive (K : Ctx B L D) (F : Set (Ev B L)) (c₁ c₂ : Clause B L D) : Prop :=
  ExclusiveNow K F c₁ c₂ ∧ ExclusiveDeferred c₁ c₂

/-- Different sections act on different events. -/
def SectionsDisjoint : List (List (Clause B L D)) → Prop
  | [] => True
  | sec :: secs => (∀ c ∈ sec, ∀ s ∈ secs, ∀ c' ∈ s, c.eff.name ≠ c'.eff.name) ∧
      SectionsDisjoint secs

theorem TopoOrdered.sectionsDisjoint {E : Ev B L → Ev B L → Prop} :
    ∀ {secs : List (List (Clause B L D))}, TopoOrdered E secs → SectionsDisjoint secs
  | [], _ => trivial
  | _ :: _, ⟨h, hr⟩ => ⟨fun c hc s hs c' hc' he =>
      h c hc s hs c' hc' (he ▸ Relation.ReflTransGen.refl), hr.sectionsDisjoint⟩

theorem fires_name {K : Ctx B L D} {W : DB B L D} {c : Clause B L D} {a : Act B L D}
    (h : fires K W c a) : a.name = c.eff.name := by
  obtain ⟨ds, -, -, rfl⟩ := h; exact Effect.act_name _ _

/-- Provenance within a section: every new action was produced by a rule of
    the section on a working set that agrees with the initial one on all
    events not acted upon by the section. -/
theorem iterate_prov (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D))
    (X : Set (Act B L D)) :
    ∀ n, ∀ a ∈ (step K D₀ sec)^[n] X, a ∈ X ∨ ∃ W : DB B L D,
      (∀ e ∉ effNames sec, ∀ as, (e, as) ∈ W ↔ (e, as) ∈ work D₀ X) ∧
      ∃ c ∈ sec, fires K W c a
  | 0, a, ha => Or.inl ha
  | n + 1, a, ha => by
    rw [Function.iterate_succ_apply'] at ha
    rcases step_cases K D₀ sec _ a ha with ha | ⟨Z, h1, h2, c, hc, hf⟩
    · exact iterate_prov K D₀ sec X n a ha
    · refine Or.inr ⟨_, fun e he as => ?_, c, hc, hf⟩
      have hXZ : X ⊆ Z := (iterate_mono K D₀ sec n X).trans h1
      refine (work_agree hXZ (fun b hb hn hname => he ?_) as).symm
      obtain ⟨c', hc', h'⟩ := iterate_new K D₀ sec (n + 1) X b
        (by rw [Function.iterate_succ_apply']; exact h2 hb) hn
      exact ⟨c', hc', h' ▸ hname⟩

/-- Invariant of a run before the remaining sections `secs`. -/
structure CFInv (K : Ctx B L D) (secs : List (List (Clause B L D))) (X : Set (Act B L D)) :
    Prop where
  cf : ConflictFree X
  cau : ∀ x, Act.cau x ∈ X → ∀ s ∈ secs, ∀ c ∈ s, ∀ W, ¬ fires K W c (.sup x)
  sup : ∀ x, Act.sup x ∈ X → ∀ s ∈ secs, ∀ c ∈ s, ∀ W, ¬ fires K W c (.cau x)

theorem SatRun.conflictFree_of_inv {K : Ctx B L D} {D₀ : DB B L D} {secs X Z}
    (h : SatRun K D₀ secs X Z) (hd : SectionsDisjoint secs)
    (hchk : ∀ sec ∈ secs, ∀ c₁ ∈ sec, ∀ c₂ ∈ sec, ExclusiveNow K (effNames sec)ᶜ c₁ c₂)
    (hinv : CFInv K secs X) : ConflictFree Z := by
  induction h with
  | nil => exact hinv.cf
  | @cons sec secs X Y Z n hY _ _ ih =>
    apply ih hd.2 (fun s hs => hchk s (List.mem_cons_of_mem _ hs))
    have hsrc := fun a (ha : a ∈ Y) => iterate_prov K D₀ sec X n a (hY ▸ ha)
    refine ⟨?_, ?_, ?_⟩
    · rintro x ⟨hc, hs⟩
      rcases hsrc _ hc with hc | ⟨W₁, hW₁, c₁, hc₁, hf₁⟩ <;>
        rcases hsrc _ hs with hs | ⟨W₂, hW₂, c₂, hc₂, hf₂⟩
      · exact hinv.cf x ⟨hc, hs⟩
      · exact hinv.cau x hc sec (List.mem_cons_self ..) c₂ hc₂ W₂ hf₂
      · exact hinv.sup x hs sec (List.mem_cons_self ..) c₁ hc₁ W₁ hf₁
      · exact hchk sec (List.mem_cons_self ..) c₁ hc₁ c₂ hc₂ W₁ W₂
          (fun e he as => (hW₁ e he as).trans (hW₂ e he as).symm) x hf₁ hf₂
    · intro x hx s hs c hc W hf
      rcases hsrc _ hx with hx | ⟨W₁, -, c₁, hc₁, hf₁⟩
      · exact hinv.cau x hx s (List.mem_cons_of_mem _ hs) c hc W hf
      · exact hd.1 c₁ hc₁ s hs c hc ((show x.1 = c₁.eff.name from fires_name hf₁).symm.trans
          (show x.1 = c.eff.name from fires_name hf))
    · intro x hx s hs c hc W hf
      rcases hsrc _ hx with hx | ⟨W₁, -, c₁, hc₁, hf₁⟩
      · exact hinv.sup x hx s (List.mem_cons_of_mem _ hs) c hc W hf
      · exact hd.1 c₁ hc₁ s hs c hc ((show x.1 = c₁.eff.name from fires_name hf₁).symm.trans
          (show x.1 = c.eff.name from fires_name hf))

/-- **Soundness of the conflict check at one time-point.**  If different
    sections act on different events, all cause/suppress pairs of a section
    are `ExclusiveNow`, and no initially due obligation can be suppressed, then
    `Saturate` never both causes and suppresses the same instance. -/
theorem conflictFree_of_exclusive {K : Ctx B L D} {D₀ : DB B L D} {secs X Z}
    (h : SatRun K D₀ secs X Z) (hd : SectionsDisjoint secs)
    (hchk : ∀ sec ∈ secs, ∀ c₁ ∈ sec, ∀ c₂ ∈ sec, ExclusiveNow K (effNames sec)ᶜ c₁ c₂)
    (hX : ∀ x, Act.sup x ∉ X)
    (hXc : ∀ x, Act.cau x ∈ X → ∀ s ∈ secs, ∀ c ∈ s, ∀ W, ¬ fires K W c (.sup x)) :
    ConflictFree Z :=
  h.conflictFree_of_inv hd hchk ⟨fun x hx => hX x hx.2, hXc, fun x hx => absurd hx (hX x)⟩

/-- Every action of a run is initial or fired by a rule. -/
theorem SatRun.fires_src {K : Ctx B L D} {D₀ : DB B L D} {secs X Z}
    (h : SatRun K D₀ secs X Z) :
    ∀ a ∈ Z, a ∈ X ∨ ∃ sec ∈ secs, ∃ c ∈ sec, ∃ W, fires K W c a := by
  induction h with
  | nil => intro a ha; exact Or.inl ha
  | @cons sec secs X Y Z n hY _ _ ih =>
    intro a ha
    rcases ih a ha with hy | ⟨s, hs, c, hc, W, hf⟩
    · rcases iterate_prov K D₀ sec X n a (hY ▸ hy) with hx | ⟨W, -, c, hc, hf⟩
      · exact Or.inl hx
      · exact Or.inr ⟨sec, List.mem_cons_self .., c, hc, W, hf⟩
    · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, c, hc, W, hf⟩

/-- **Soundness of the conflict check for the enforcement loop.**  Under the
    per-section and deferred checks, no output time-point both causes and
    suppresses an instance. -/
theorem LoopRun.conflictFree {P : Program B L D} {σ : Tr B L D} {v₀ : ℕ → D}
    (R : LoopRun P σ v₀) (hd : SectionsDisjoint P.secs)
    (hchk : ∀ j, ∀ sec ∈ P.secs, ∀ c₁ ∈ sec, ∀ c₂ ∈ sec, ExclusiveNow (R.K j) (effNames sec)ᶜ c₁ c₂)
    (hdef : ∀ c₁ ∈ P.rules, ∀ c₂ ∈ P.rules, ExclusiveDeferred c₁ c₂) :
    ∀ j, ConflictFree (R.X j) := by
  intro j
  apply conflictFree_of_exclusive (R.run j) hd (hchk j)
  · intro x hx
    obtain ⟨y, hy, -⟩ := R.initSrc j _ hx
    cases hy
  · intro x hx s hs c hc W hf
    obtain ⟨y, hy, i, hi⟩ := R.initSrc j _ hx
    cases hy
    -- the obligation was fired as a deferred action by some rule at time-point `i`
    have hdefd : ∃ a ∈ R.X i, a.deferred = some x := by
      rcases hi with ⟨b, hb⟩ | ⟨n, t, hn⟩
      · exact ⟨_, hb, rfl⟩
      · exact ⟨_, hn, rfl⟩
    obtain ⟨a, ha, hax⟩ := hdefd
    rcases (R.run i).fires_src a ha with hinit | ⟨s₁, hs₁, c₁, hc₁, W₁, hf₁⟩
    · obtain ⟨y, rfl, -⟩ := R.initSrc i a hinit
      cases hax
    · exact hdef c₁ (List.mem_flatten.2 ⟨s₁, hs₁, hc₁⟩) c (List.mem_flatten.2 ⟨s, hs, hc⟩)
        (R.K i) (R.K j) W₁ W a x hf₁ hax hf

/-- The conflict check for every rule of each section against every rule of
    the program yields the immediate checks within sections and the deferred
    checks for all pairs. -/
theorem Exclusive.split {secs : List (List (Clause B L D))} {K : ℕ → Ctx B L D}
    (h : ∀ j, ∀ sec ∈ secs, ∀ c₁ ∈ sec, ∀ c₂ ∈ secs.flatten, Exclusive (K j) (effNames sec)ᶜ c₁ c₂) :
    (∀ j, ∀ sec ∈ secs, ∀ c₁ ∈ sec, ∀ c₂ ∈ sec, ExclusiveNow (K j) (effNames sec)ᶜ c₁ c₂) ∧
      ∀ c₁ ∈ secs.flatten, ∀ c₂ ∈ secs.flatten, ExclusiveDeferred c₁ c₂ := by
  refine ⟨fun j sec hs c₁ h₁ c₂ h₂ =>
    (h j sec hs c₁ h₁ c₂ (List.mem_flatten.2 ⟨sec, hs, h₂⟩)).1, fun c₁ h₁ c₂ h₂ => ?_⟩
  obtain ⟨sec, hs, h₁⟩ := List.mem_flatten.1 h₁
  exact (h 0 sec hs c₁ h₁ c₂ h₂).2

/-! ## The conflict check on the EDG

The compiler (`src/smt_check.ml`) decides `Exclusive` on the EDG: for every
event, every rule causing it is paired with every rule suppressing it, and the
pair is passed to an SMT solver as a single formula, the *conflict query*: the
two triggers, each over its own copy of the variables and of the predicates,
and the equality of the two effects' arguments.  The two copies share only the
events strictly upstream of the section (nothing if the cause is deferred).  An
event that is not both caused and suppressed needs no query.

We assume a sound solver for MFOTL (`SMT`): if it reports a formula
unsatisfiable, no single database satisfies it.  `ConflictCheck.exclusive`
proves that a successful check establishes `Exclusive`. -/

/-- Labels of the EDG edges into `e` contributed by rule `c`: `c` causes,
    suppresses, or causes `e` at a later time-point. -/
def Clause.Causes (c : Clause B L D) (e : Ev B L) : Prop := ∃ ts, c.eff = .cau e ts
def Clause.Sups (c : Clause B L D) (e : Ev B L) : Prop := ∃ ts, c.eff = .sup e ts
def Clause.Defers (c : Clause B L D) (e : Ev B L) : Prop :=
  ∃ ts, (∃ b, c.eff = .later b e ts) ∨ ∃ n t, c.eff = .next n t e ts

/-- A sound SMT solver for MFOTL formulas (trusted): a formula reported
    unsatisfiable has no model (a database, a let interpretation, and a
    valuation). -/
structure SMT (B L D : Type u) where
  unsat : Fm B L D → Prop
  sound : ∀ φ, unsat φ → ∀ (W : DB B L D) lv v, ¬ (ptTr W lv).sat 0 v φ

/-! ### The conflict query -/

/-- Predicate symbols of a conflict query: shared events, and the events and
    lets of one side (`false`: the causing rule, `true`: the suppressing one). -/
inductive QSym (B L : Type u) where
  | shared : Ev B L → QSym B L
  | priv : Bool → Pr B L → QSym B L

/-- Formulas of conflict queries: predicates are `QSym`s (as let predicates). -/
abbrev QFm (B L D : Type u) := Fm PEmpty.{u+1} (QSym B L) D

/-- Rename the predicate symbols of a formula. -/
def Fm.rename {B' L' : Type u} (f : Pr B L → Pr B' L') : Fm B L D → Fm B' L' D
  | .tt => .tt
  | .pred p ts => .pred (f p) ts
  | .eq t u => .eq t u
  | .neg φ => .neg (φ.rename f)
  | .conj φ ψ => .conj (φ.rename f) (ψ.rename f)
  | .ex φ => .ex (φ.rename f)
  | .ev a b φ => .ev a b (φ.rename f)
  | .nx a b φ => .nx a b (φ.rename f)

theorem sat_rename {B' L' : Type u} (f : Pr B L → Pr B' L') {W : DB B L D} {lv}
    {W' : DB B' L' D} {lv'}
    (h : ∀ i p as, (ptTr W' lv').prIn i (f p) as ↔ (ptTr W lv).prIn i p as) :
    ∀ (φ : Fm B L D) i v, (ptTr W' lv').sat i v (φ.rename f) ↔ (ptTr W lv).sat i v φ := by
  intro φ
  induction φ with
  | tt => intros; rfl
  | pred p ts => intro i v; exact h i p _
  | eq => intros; rfl
  | neg φ ih => intro i v; simp only [Fm.rename, Tr.sat, ih]
  | conj φ ψ ih₁ ih₂ => intro i v; simp only [Fm.rename, Tr.sat, ih₁, ih₂]
  | ex φ ih => intro i v; simp only [Fm.rename, Tr.sat, ih]
  | ev a b φ ih => intro i v; simp only [Fm.rename, Tr.sat]; exact exists_congr fun j => by rw [ih j v]; rfl
  | nx a b φ ih => intro i v; simp only [Fm.rename, Tr.sat]; rw [ih (i + 1) v]; rfl

/-- A trigger as a formula. -/
def Trigger.toFm (θ : Trigger B L D) : Fm B L D := .conj θ.guards.toFm θ.filter

theorem Trigger.sat_toFm (σ : Tr B L D) (i : ℕ) (v : ℕ → D) (θ : Trigger B L D) :
    σ.sat i v θ.toFm ↔ θ.sat σ i v := by
  simp only [Trigger.toFm, Tr.sat, Guards.sat_toFm, Trigger.sat]

/-- The variables of side `b`: `x` becomes `2x` (`b = false`) or `2x+1`. -/
def sideS (b : Bool) : ℕ → Term D := fun n => .var (2 * n + if b then 1 else 0)

/-- The valuation of a query from the valuations of the two sides. -/
def merge (w₁ w₂ : ℕ → D) : ℕ → D := fun n => if n % 2 = 0 then w₁ (n / 2) else w₂ (n / 2)

theorem eval_sideS (b : Bool) (w₁ w₂ : ℕ → D) (n : ℕ) :
    (sideS b n).eval (merge w₁ w₂) = (if b then w₂ else w₁) n := by
  cases b
  · show (if (2 * n + 0) % 2 = 0 then w₁ ((2 * n + 0) / 2) else w₂ ((2 * n + 0) / 2)) = w₁ n
    rw [if_pos (by omega)]; congr 1; omega
  · show (if (2 * n + 1) % 2 = 0 then w₁ ((2 * n + 1) / 2) else w₂ ((2 * n + 1) / 2)) = w₂ n
    rw [if_neg (by omega)]; congr 1; omega

open Classical in
/-- The predicate symbols of side `b`, sharing the events in `sh`. -/
noncomputable def qsym (sh : Set (Ev B L)) (b : Bool) : Pr B L → Pr PEmpty.{u+1} (QSym B L)
  | .ev e => .lp (if e ∈ sh then .shared e else .priv b (.ev e))
  | .lp p => .lp (.priv b (.lp p))

/-- Side `b` of a query. -/
noncomputable def qside (sh : Set (Ev B L)) (b : Bool) (φ : Fm B L D) : QFm B L D :=
  (φ.subst (sideS b)).rename (qsym sh b)

/-- Equality of the effect arguments of the two sides. -/
def argsEq : List (Term D) → List (Term D) → QFm B L D
  | t :: ts, u :: us => .conj (.eq (t.subst (sideS false)) (u.subst (sideS true))) (argsEq ts us)
  | _, _ => .tt

/-- **The conflict query** for rules `c₁` (causing) and `c₂` (suppressing),
    sharing the events in `sh`. -/
noncomputable def query (sh : Set (Ev B L)) (c₁ c₂ : Clause B L D) : QFm B L D :=
  .conj (qside sh false c₁.trig.toFm)
    (.conj (qside sh true c₂.trig.toFm) (argsEq c₁.eff.args c₂.eff.args))

/-! ### Soundness of the query -/

section
variable (W₁ W₂ : DB B L D) (lv₁ lv₂ : L → List D → Prop)

/-- The model of a query built from the working sets of the two sides. -/
def qlv : QSym B L → List D → Prop
  | .shared e, as => (e, as) ∈ W₁
  | .priv false p, as => (ptTr W₁ lv₁).prIn 0 p as
  | .priv true p, as => (ptTr W₂ lv₂).prIn 0 p as

end

theorem sat_qside {sh : Set (Ev B L)} {W₁ W₂ : DB B L D} {lv₁ lv₂ : L → List D → Prop}
    (hag : ∀ e ∈ sh, ∀ as, (e, as) ∈ W₁ ↔ (e, as) ∈ W₂) (w₁ w₂ : ℕ → D) (b : Bool)
    (φ : Fm B L D) :
    (ptTr ∅ (qlv W₁ W₂ lv₁ lv₂)).sat 0 (merge w₁ w₂) (qside sh b φ) ↔
      (ptTr (if b then W₂ else W₁) (if b then lv₂ else lv₁)).sat 0 (if b then w₂ else w₁) φ := by
  rw [qside, sat_rename (W := if b then W₂ else W₁) (lv := if b then lv₂ else lv₁), Tr.sat_subst]
  · have : (fun n => (sideS b n).eval (merge w₁ w₂)) = (if b then w₂ else w₁) := by
      funext n; rw [eval_sideS]
    rw [this]
  · intro i p as
    classical
    cases p with
    | ev e =>
      by_cases he : e ∈ sh
      · simp only [qsym, if_pos he, Tr.prIn, ptTr, qlv]
        cases b
        · rfl
        · exact hag e he as
      · simp only [qsym, if_neg he, Tr.prIn, ptTr, qlv]
        cases b <;> rfl
    | lp p => cases b <;> rfl

theorem sat_argsEq {W : DB PEmpty.{u+1} (QSym B L) D} {lv} (w₁ w₂ : ℕ → D) :
    ∀ ts us : List (Term D), ts.map (Term.eval w₁) = us.map (Term.eval w₂) →
      (ptTr W lv).sat 0 (merge w₁ w₂) (argsEq ts us : QFm B L D)
  | t :: ts, u :: us, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    refine ⟨?_, sat_argsEq w₁ w₂ ts us h.2⟩
    show (t.subst (sideS false)).eval (merge w₁ w₂) = (u.subst (sideS true)).eval (merge w₁ w₂)
    have e₁ : (fun n => (sideS false n).eval (merge w₁ w₂)) = w₁ :=
      funext fun n => by simpa using eval_sideS false w₁ w₂ n
    have e₂ : (fun n => (sideS true n).eval (merge w₁ w₂)) = w₂ :=
      funext fun n => by simpa using eval_sideS true w₁ w₂ n
    rw [Term.eval_subst, Term.eval_subst, e₁, e₂]; exact h.1
  | [], _, _ | _ :: _, [], _ => trivial

/-- **Soundness of the query.**  If the cause of `c₁` on `W₁` and the
    suppression of `c₂` on `W₂` concern the same instance, and the two working
    sets agree on the shared events, the conflict query is satisfiable. -/
theorem query_sat {sh : Set (Ev B L)} {c₁ c₂ : Clause B L D} {W₁ W₂ : DB B L D}
    {lv₁ lv₂ : L → List D → Prop} (hag : ∀ e ∈ sh, ∀ as, (e, as) ∈ W₁ ↔ (e, as) ∈ W₂)
    {w₁ w₂ : ℕ → D} (h₁ : c₁.trig.sat (ptTr W₁ lv₁) 0 w₁) (h₂ : c₂.trig.sat (ptTr W₂ lv₂) 0 w₂)
    (hargs : c₁.eff.args.map (Term.eval w₁) = c₂.eff.args.map (Term.eval w₂)) :
    (ptTr ∅ (qlv W₁ W₂ lv₁ lv₂)).sat 0 (merge w₁ w₂) (query sh c₁ c₂) := by
  refine ⟨?_, ?_, sat_argsEq w₁ w₂ _ _ hargs⟩
  · rw [sat_qside hag]; exact (Trigger.sat_toFm _ _ _ _).2 h₁
  · rw [sat_qside hag]; exact (Trigger.sat_toFm _ _ _ _).2 h₂

/-- Firing a cause or a suppression determines the effect. -/
theorem fires_cau {K : Ctx B L D} {W : DB B L D} {c : Clause B L D} {x}
    (h : fires K W c (.cau x)) : ∃ ds ts, c.trig.sat (ptTr W (K.lv W)) 0 (vapp ds K.v₀) ∧
      c.eff = .cau x.1 ts ∧ x.2 = ts.map (Term.eval (vapp ds K.v₀)) := by
  obtain ⟨ds, -, ht, hx⟩ := h
  cases he : c.eff with
  | cau e ts => rw [he] at hx; cases hx; exact ⟨ds, ts, ht, rfl, rfl⟩
  | sup | later | next => rw [he] at hx; cases hx

theorem fires_sup {K : Ctx B L D} {W : DB B L D} {c : Clause B L D} {x}
    (h : fires K W c (.sup x)) : ∃ ds ts, c.trig.sat (ptTr W (K.lv W)) 0 (vapp ds K.v₀) ∧
      c.eff = .sup x.1 ts ∧ x.2 = ts.map (Term.eval (vapp ds K.v₀)) := by
  obtain ⟨ds, -, ht, hx⟩ := h
  cases he : c.eff with
  | sup e ts => rw [he] at hx; cases hx; exact ⟨ds, ts, ht, rfl, rfl⟩
  | cau | later | next => rw [he] at hx; cases hx

theorem fires_deferred {K : Ctx B L D} {W : DB B L D} {c : Clause B L D} {a x}
    (h : fires K W c a) (hd : a.deferred = some x) :
    ∃ ds ts, c.trig.sat (ptTr W (K.lv W)) 0 (vapp ds K.v₀) ∧ c.Defers x.1 ∧
      c.eff.args = ts ∧ x.2 = ts.map (Term.eval (vapp ds K.v₀)) := by
  obtain ⟨ds, -, ht, rfl⟩ := h
  cases he : c.eff with
  | later b e ts =>
    rw [he] at hd; cases hd; exact ⟨ds, ts, ht, ⟨ts, Or.inl ⟨b, he⟩⟩, rfl, rfl⟩
  | next n t e ts =>
    rw [he] at hd; cases hd; exact ⟨ds, ts, ht, ⟨ts, Or.inr ⟨n, t, he⟩⟩, rfl, rfl⟩
  | cau | sup => rw [he] at hd; cases hd

/-- A solver-certified query gives `ExclusiveNow`, if the shared events are
    not acted upon by the section. -/
theorem exclusiveNow_of_smt {S : SMT PEmpty.{u+1} (QSym B L) D} {sh F : Set (Ev B L)}
    (hsh : sh ⊆ F) {K : Ctx B L D} {c₁ c₂ : Clause B L D}
    (h : ∀ e, c₁.Causes e → c₂.Sups e → S.unsat (query sh c₁ c₂)) :
    ExclusiveNow K F c₁ c₂ := by
  intro W₁ W₂ hag x hc hs
  obtain ⟨ds₁, ts₁, ht₁, he₁, hx₁⟩ := fires_cau hc
  obtain ⟨ds₂, ts₂, ht₂, he₂, hx₂⟩ := fires_sup hs
  refine S.sound _ (h x.1 ⟨ts₁, he₁⟩ ⟨ts₂, he₂⟩) ∅ _ _
    (query_sat (fun e he as => hag e (hsh he) as) ht₁ ht₂ ?_)
  rw [he₁, he₂]; exact hx₁.symm.trans hx₂

/-- A solver-certified query without shared events gives `ExclusiveDeferred`. -/
theorem exclusiveDeferred_of_smt {S : SMT PEmpty.{u+1} (QSym B L) D} {c₁ c₂ : Clause B L D}
    (h : ∀ e, c₁.Defers e → c₂.Sups e → S.unsat (query ∅ c₁ c₂)) :
    ExclusiveDeferred c₁ c₂ := by
  intro K₁ K₂ W₁ W₂ a x hf hd hs
  obtain ⟨ds₁, ts₁, ht₁, hD, ha₁, hx₁⟩ := fires_deferred hf hd
  obtain ⟨ds₂, ts₂, ht₂, he₂, hx₂⟩ := fires_sup hs
  refine S.sound _ (h x.1 hD ⟨ts₂, he₂⟩) ∅ _ _
    (query_sat (fun _ he => he.elim) ht₁ ht₂ ?_)
  rw [ha₁, he₂]; exact hx₁.symm.trans hx₂

/-! ### The check -/

open Relation in
/-- The events shared by the queries of a section: the events strictly
    upstream of it in the EDG. -/
def Up (ld : L → List (Ev B L)) (rules : List (Clause B L D)) (sec : List (Clause B L D)) :
    Set (Ev B L) :=
  {e | e ∉ effNames sec ∧ ∃ c ∈ sec, ReflTransGen (EDG ld rules) e c.eff.name}

/-- **The conflict check** (paper, Section 4.5; `src/smt_check.ml`): for every
    rule causing an event and every rule suppressing it, the solver reports the
    conflict query unsatisfiable, sharing the events upstream of the section
    (immediate cause) or nothing (deferred cause). -/
structure ConflictCheck (S : SMT PEmpty.{u+1} (QSym B L) D) (ld : L → List (Ev B L))
    (rules : List (Clause B L D)) (secs : List (List (Clause B L D))) : Prop where
  now : ∀ sec ∈ secs, ∀ c₁ ∈ sec, ∀ c₂ ∈ rules, ∀ e, c₁.Causes e → c₂.Sups e →
    S.unsat (query (Up ld rules sec) c₁ c₂)
  deferred : ∀ c₁ ∈ rules, ∀ c₂ ∈ rules, ∀ e, c₁.Defers e → c₂.Sups e →
    S.unsat (query ∅ c₁ c₂)

/-- **Soundness of the conflict check.**  A successful check establishes the
    semantic property `Exclusive`, in any evaluation context. -/
theorem ConflictCheck.exclusive {S : SMT PEmpty.{u+1} (QSym B L) D} {ld : L → List (Ev B L)}
    {rules : List (Clause B L D)} {secs : List (List (Clause B L D))}
    (h : ConflictCheck S ld rules secs) (hsub : ∀ sec ∈ secs, ∀ c ∈ sec, c ∈ rules)
    (K : Ctx B L D) : ∀ sec ∈ secs, ∀ c₁ ∈ sec, ∀ c₂ ∈ rules,
      Exclusive K (effNames sec)ᶜ c₁ c₂ :=
  fun sec hs c₁ h₁ c₂ h₂ =>
    ⟨exclusiveNow_of_smt (fun _ he => he.1) (h.now sec hs c₁ h₁ c₂ h₂),
     exclusiveDeferred_of_smt (h.deferred c₁ (hsub sec hs c₁ h₁) c₂ h₂)⟩

/-- Without an event that is both caused (or deferred) and suppressed, the
    check needs no query. -/
theorem ConflictCheck.of_noConflict {S : SMT PEmpty.{u+1} (QSym B L) D}
    {ld : L → List (Ev B L)} {rules : List (Clause B L D)} {secs : List (List (Clause B L D))}
    (hnow : ∀ sec ∈ secs, ∀ c₁ ∈ sec, ∀ c₂ ∈ rules, ∀ e, c₁.Causes e → ¬ c₂.Sups e)
    (hdef : ∀ c₁ ∈ rules, ∀ c₂ ∈ rules, ∀ e, c₁.Defers e → ¬ c₂.Sups e) :
    ConflictCheck S ld rules secs :=
  ⟨fun sec hs c₁ h₁ c₂ h₂ e hc hsup => absurd hsup (hnow sec hs c₁ h₁ c₂ h₂ e hc),
   fun c₁ h₁ c₂ h₂ e hc hsup => absurd hsup (hdef c₁ h₁ c₂ h₂ e hc)⟩

end Enfflash
