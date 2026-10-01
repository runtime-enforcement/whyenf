/-
  EnfFlash formalization — the EF `Saturate` loop at one time-point
  (paper, Section 3.2, Algorithm 2) and its correctness:

  * `saturate_sound`: after running the (stratified) sections to their
    fixpoints, every rule is satisfied by the resulting working set
    `(D ∖ S) ∪ C`, provided no event is both caused and suppressed;
  * `fixpoint_exists`: a fixpoint section terminates after at most `|U|`
    iterations whenever all rule instances lie in a finite universe `U`
    (e.g. because all effect terms are stable, see `Dataflow.lean`).
-/
import Enfflash.EF
import Mathlib.Data.Set.Card

namespace Enfflash

universe u
variable {B L D : Type u}

/-! ### Dependencies and stratification -/

theorem iterate_mono (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D)) :
    ∀ (n : ℕ) (X : Set (Act B L D)), X ⊆ (step K D₀ sec)^[n] X
  | 0, _ => le_rfl
  | n + 1, X => by
    rw [Function.iterate_succ_apply']
    exact (iterate_mono K D₀ sec n X).trans (subset_step K D₀ sec _)

/-- New actions of a section come from its rules. -/
theorem iterate_new (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D)) :
    ∀ (n : ℕ) (X : Set (Act B L D)), ∀ a ∈ (step K D₀ sec)^[n] X, a ∉ X →
      ∃ c ∈ sec, a.name = c.eff.name
  | 0, _, a, ha, hn => absurd ha hn
  | n + 1, X, a, ha, hn => by
    rw [Function.iterate_succ_apply'] at ha
    rcases step_cases K D₀ sec _ a ha with ha | ⟨-, -, -, c, hc, ds, -, -, rfl⟩
    · exact iterate_new K D₀ sec n X a ha hn
    · exact ⟨c, hc, Effect.act_name _ _⟩

theorem SatRun.mono {K : Ctx B L D} {D₀} {secs X Z} (h : SatRun K D₀ secs X Z) : X ⊆ Z := by
  induction h with
  | nil => exact le_rfl
  | cons n hY _ _ ih => exact (hY ▸ iterate_mono K D₀ _ n _).trans ih

theorem SatRun.new {K : Ctx B L D} {D₀} {secs X Z} (h : SatRun K D₀ secs X Z) :
    ∀ a ∈ Z, a ∉ X → ∃ sec ∈ secs, ∃ c ∈ sec, a.name = c.eff.name := by
  induction h with
  | nil => intro a ha hn; exact absurd ha hn
  | @cons sec secs X Y Z n hY _ _ ih =>
    intro a ha hn
    by_cases hy : a ∈ Y
    · obtain ⟨c, hc, he⟩ := iterate_new K D₀ sec n X a (hY ▸ hy) hn
      exact ⟨sec, List.mem_cons_self .., c, hc, he⟩
    · obtain ⟨s, hs, c, hc, he⟩ := ih a ha hy
      exact ⟨s, List.mem_cons_of_mem _ hs, c, hc, he⟩

/-- Working sets agree on all names not touched by new actions. -/
theorem work_agree {D₀ : DB B L D} {X Z : Set (Act B L D)} (hXZ : X ⊆ Z) {e : Ev B L}
    (he : ∀ a ∈ Z, a ∉ X → a.name ≠ e) (as : List D) :
    (e, as) ∈ work D₀ X ↔ (e, as) ∈ work D₀ Z := by
  have hs : Act.sup (e, as) ∈ X ↔ Act.sup (e, as) ∈ Z :=
    ⟨fun h => hXZ h, fun h => by_contra fun hn => he _ h hn rfl⟩
  have hc : Act.cau (e, as) ∈ X ↔ Act.cau (e, as) ∈ Z :=
    ⟨fun h => hXZ h, fun h => by_contra fun hn => he _ h hn rfl⟩
  simp only [work, Set.mem_setOf_eq, hs, hc]

/-- Stratification (the EDG order of sections): no rule of a later section
    produces an event on which a rule of an earlier section depends. -/
def Stratified (K : Ctx B L D) : List (List (Clause B L D)) → Prop
  | [] => True
  | sec :: secs => (∀ c ∈ sec, ∃ N, TrigDeps K c N ∧
      ∀ s ∈ secs, ∀ c' ∈ s, c'.eff.name ∉ N) ∧ Stratified K secs

/-- **Soundness of `Saturate`.**  After a stratified run, every rule of every
    section is saturated w.r.t. the final working set. -/
theorem saturate_sound {K : Ctx B L D} {D₀} {secs X Z} (h : SatRun K D₀ secs X Z)
    (hs : Stratified K secs) :
    ∀ sec ∈ secs, ∀ c ∈ sec, ∀ a, fires K (work D₀ Z) c a → a ∈ Z := by
  induction h with
  | nil => intro sec hsec; simp at hsec
  | @cons sec secs X Y Z n hY hfix hrest ih =>
    intro s hs' c hc a ha
    rcases List.mem_cons.1 hs' with rfl | hs'
    · obtain ⟨N, hdeps, hN⟩ := hs.1 c hc
      obtain ⟨ds, hds, htr, rfl⟩ := ha
      apply hrest.mono
      apply hfix c hc
      refine ⟨ds, hds, ?_, rfl⟩
      refine (hdeps _ _ (fun e he as => ?_) _).2 htr
      apply work_agree hrest.mono
      intro a ha hn hname
      obtain ⟨s', hs'', c', hc', he'⟩ := hrest.new a ha hn
      exact hN s' hs'' c' hc' (he' ▸ hname ▸ he)
    · exact ih hs.2 s hs' c hc a ha

/-- A `once` section whose rules do not depend on the section's own effects
    reaches its fixpoint after a single pass. -/
theorem once_fixed (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D))
    (X : Set (Act B L D))
    (hdep : ∀ c ∈ sec, ∃ N, TrigDeps K c N ∧ ∀ c' ∈ sec, c'.eff.name ∉ N) :
    Fixed K D₀ sec (step K D₀ sec X) := by
  intro c hc a ⟨ds, hds, htr, ha⟩
  obtain ⟨N, hdeps, hN⟩ := hdep c hc
  obtain ⟨Z, hXZ, hZ, hup⟩ := step_rule K D₀ sec X c hc
  refine hup (Or.inr ⟨ds, hds, (hdeps _ _ (fun e he as => ?_) _).2 htr, ha⟩)
  apply work_agree hZ
  intro b hb hn hname
  rcases step_cases K D₀ sec X b hb with hx | ⟨-, -, -, c', hc', ds', -, -, rfl⟩
  · exact hn (hXZ hx)
  · exact hN c' hc' (by rw [Effect.act_name] at hname; rw [hname]; exact he)

/-! ### Immediate effects hold in the output -/

/-- If the rule set is saturated and conflict-free, then in a trace whose
    time-point `i` is the final working set, every clause holds as far as its
    immediate effects are concerned, and deferred effects are registered as
    obligations. -/
theorem clause_holds_point {K : Ctx B L D} {D₀ : DB B L D} {Z : Set (Act B L D)}
    (hcf : ConflictFree Z) {c : Clause B L D} (hpres : c.trig.filter.present)
    (hsat : ∀ a, fires K (work D₀ Z) c a → a ∈ Z)
    {σ : Tr B L D} {i : ℕ} (hdb : σ.db i = work D₀ Z) (hlv : σ.lv i = K.lv (work D₀ Z)) :
    ∀ ds : List D, ds.length = c.nloc → c.trig.sat σ i (vapp ds K.v₀) →
      (match c.eff with
       | .cau _ _ | .sup _ _ => c.eff.holds σ i (vapp ds K.v₀)
       | _ => True) ∧ c.eff.act (vapp ds K.v₀) ∈ Z := by
  intro ds hds htr
  have htr' : c.trig.sat (ptTr (work D₀ Z) (K.lv (work D₀ Z))) 0 (vapp ds K.v₀) := by
    refine ⟨?_, (Tr.sat_present σ _ i 0 hdb hlv _ hpres _).1 htr.2⟩
    obtain ⟨κ, hκ, hall⟩ := htr.1
    refine ⟨κ, hκ, fun a ha => ?_⟩
    have := hall a ha
    cases a with
    | pred p ts => cases p <;> simpa [GAtom.sat, Tr.prIn, ptTr, hdb, hlv] using this
    | eq t d => exact this
  have hin := hsat _ ⟨ds, hds, htr', rfl⟩
  refine ⟨?_, hin⟩
  cases he : c.eff with
  | cau e ts =>
    rw [he] at hin
    simp only [Effect.holds, hdb, work, Set.mem_setOf_eq]
    exact Or.inr hin
  | sup e ts =>
    rw [he] at hin
    simp only [Effect.holds, hdb, work, Set.mem_setOf_eq, not_or, not_and, not_not]
    exact ⟨fun _ => hin, fun hc => hcf _ ⟨hc, hin⟩⟩
  | later => trivial
  | next => trivial

/-! ### Termination of fixpoint sections -/

/-- If every action ever produced lies in a finite universe `U` containing the
    initial set, iterating a section reaches a fixpoint after at most `|U|`
    passes (the sets `C`, `S`, `Ω` only grow). -/
theorem fixpoint_exists (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D))
    (U : Set (Act B L D)) (hU : U.Finite) (X : Set (Act B L D)) (hX : X ⊆ U)
    (hclosed : ∀ Y ⊆ U, ∀ c ∈ sec, ∀ a, fires K (work D₀ Y) c a → a ∈ U) :
    ∃ n ≤ U.ncard, Fixed K D₀ sec ((step K D₀ sec)^[n] X) ∧ (step K D₀ sec)^[n] X ⊆ U := by
  set f := step K D₀ sec
  have hsub : ∀ n, f^[n] X ⊆ U := by
    intro n; induction n with
    | zero => exact hX
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact step_induct K D₀ (· ⊆ U) sec (fun c hc Y hY => Set.union_subset hY
        fun a ha => hclosed Y hY c hc a ha) _ ih
  suffices h : ∃ n ≤ U.ncard, Fixed K D₀ sec (f^[n] X) by
    obtain ⟨n, hn, hfix⟩ := h; exact ⟨n, hn, hfix, hsub n⟩
  by_contra hne
  push Not at hne
  -- the iterates grow strictly, so their cardinality exceeds |U|
  have hgrow : ∀ n ≤ U.ncard + 1, n ≤ (f^[n] X).ncard := by
    intro n hn
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have ih := ih (by omega)
      have hne' : f (f^[n] X) ≠ f^[n] X := fun h =>
        hne n (by omega) ((step_eq_iff_fixed K D₀ sec _).1 h)
      have hss : f^[n] X ⊂ f (f^[n] X) :=
        Set.ssubset_iff_subset_ne.2 ⟨subset_step K D₀ sec _, fun h => hne' h.symm⟩
      rw [Function.iterate_succ_apply']
      have := Set.ncard_lt_ncard hss (hU.subset (by
        rw [← Function.iterate_succ_apply' f n X]; exact hsub (n + 1)))
      omega
  have h1 := hgrow (U.ncard + 1) le_rfl
  have h2 := Set.ncard_le_ncard (hsub (U.ncard + 1)) hU
  omega

end Enfflash
