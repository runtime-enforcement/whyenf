/-
  Enfflash formalization — soundness of the cause/suppress conflict check
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

theorem RankOrdered.sectionsDisjoint {rk : Ev B L → ℕ} :
    ∀ {secs : List (List (Clause B L D))}, RankOrdered rk secs → SectionsDisjoint secs
  | [], _ => trivial
  | _ :: _, ⟨h, hr⟩ => ⟨fun c hc s hs c' hc' he => by
      have := h c hc s hs c' hc'; rw [he] at this; omega, hr.sectionsDisjoint⟩

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

end Enfflash
