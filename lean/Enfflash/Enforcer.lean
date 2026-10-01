/-
  EnfFlash formalization — the proactive enforcement loop (paper, Section 2.3,
  Algorithm 1, with `μ`/`ν` from Algorithm 2) and the main correctness theorem
  (Theorem 4.5, "Compilation correctness").

  The loop is specified by the properties of its output trace (`LoopRun`):
  every output time-point is the result of a stratified `Saturate` run
  starting from the obligations due at that time-point, and obligations are
  discharged on time:

  * `[delay b]` obligations created at time-point `i` are caused at the
    proactive time-point that `ν` inserts for timestamp `τ_i + b` (the last
    time-point with that timestamp);
  * `[next n]` obligations are caused at time-point `i + n` (`μ` and `ν`
    discharge due ones; `ν` inserts a time-point whenever something is due);
    for a single `[next 1]` obligation the next time-point is at most one
    time unit later, as `ν` is called for every timestamp.
-/
import Enfflash.Saturate
import Enfflash.Realize

namespace Enfflash

universe u
variable {B L D : Type u}

/-- Every rule of the program holds at every time-point of the output. -/
theorem LoopRun.clauses_hold {P : Program B L D} {σ : Tr B L D} {v₀ : ℕ → D}
    (R : LoopRun P σ v₀) (hstrat : ∀ j, Stratified (R.K j) P.secs)
    (hcf : ∀ j, ConflictFree (R.X j)) (hpres : ∀ c ∈ P.rules, c.trig.filter.present) :
    ∀ j, ∀ c ∈ P.rules, c.holds σ j v₀ := by
  intro j c hc ds hds htr
  obtain ⟨sec, hsec, hcs⟩ := List.mem_flatten.1 hc
  have hsat := saturate_sound (R.run j) (hstrat j) sec hsec c hcs
  have hv := R.hv₀ j
  rw [← hv] at htr ⊢
  obtain ⟨himm, hact⟩ := clause_holds_point (hcf j) (hpres c hc) hsat (R.db j) ((R.lv j).trans (by rw [R.db j])) ds hds htr
  cases he : c.eff with
  | cau e ts => rw [he] at himm; exact himm
  | sup e ts => rw [he] at himm; exact himm
  | later b e ts =>
    rw [he] at hact
    obtain ⟨j', hlast, hin⟩ := R.laterFire j b _ hact
    refine ⟨j', hlast, ?_⟩
    rw [R.db j']
    exact Or.inr ((R.run j').mono hin)
  | next n t e ts =>
    rw [he] at hact
    obtain ⟨htime, hin⟩ := R.nextFire j n t _ hact
    refine ⟨htime, ?_⟩
    rw [R.db (j + n)]
    exact Or.inr ((R.run (j + n)).mono hin)

theorem iterate_src (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D)) :
    ∀ (n : ℕ) (X : Set (Act B L D)), ∀ a ∈ (step K D₀ sec)^[n] X,
      a ∈ X ∨ ∃ c ∈ sec, ∃ w, a = c.eff.act w
  | 0, _, a, ha => Or.inl ha
  | n + 1, X, a, ha => by
    rw [Function.iterate_succ_apply'] at ha
    rcases step_cases K D₀ sec _ a ha with ha | ⟨-, -, -, c, hc, ds, -, -, rfl⟩
    · exact iterate_src K D₀ sec n X a ha
    · exact Or.inr ⟨c, hc, _, rfl⟩

/-- Every action of a run is initial or produced by a rule. -/
theorem SatRun.src {K : Ctx B L D} {D₀ : DB B L D} {secs X Z} (h : SatRun K D₀ secs X Z) :
    ∀ a ∈ Z, a ∈ X ∨ ∃ sec ∈ secs, ∃ c ∈ sec, ∃ w, a = c.eff.act w := by
  induction h with
  | nil => intro a ha; exact Or.inl ha
  | @cons sec secs X Y Z n hY _ _ ih =>
    intro a ha
    rcases ih a ha with hy | ⟨s, hs, c, hc, w, rfl⟩
    · rcases iterate_src K D₀ sec n X a (hY ▸ hy) with hx | ⟨c, hc, w, rfl⟩
      · exact Or.inl hx
      · exact Or.inr ⟨sec, List.mem_cons_self .., c, hc, w, rfl⟩
    · exact Or.inr ⟨s, List.mem_cons_of_mem _ hs, c, hc, w, rfl⟩

/-! ### Main theorem -/

/-- **Compilation correctness (paper, Theorem `thm:compile`).**  Let `□χ` be in let-normal
    form with lets `Γ`, `R` a valid realization, `C` a candidate clause set
    for `χ`, and `P` an EF program whose rules comprise `C` and all gated
    realization clauses, all with present filters.  On every output `σ` of the
    enforcement loop with `P` (stratified sections, no cause/suppress
    conflicts, tables computing the lets' meaning), `□χ` holds. -/
theorem enforcer_sound {S : Sig B L D} {Γ : L → Option (LetDef B L D)} {R : Real B L D}
    {r : L → L → Prop} (hwf : WellFounded r) (hV : R.Valid S Γ r)
    {χ : Fm B L D} {CS : List (List (Clause B L D))}
    (hrw : Rw (R.scope S (fun _ => True)) true χ CS) {C : List (Clause B L D)} (hC : C ∈ CS)
    (P : Program B L D) (hPC : ∀ c ∈ C, c ∈ P.rules)
    (hPR : ∀ c, R.clauses S.ar c → c ∈ P.rules)
    (hpres : ∀ c ∈ P.rules, c.trig.filter.present)
    {σ : Tr B L D} {v₀ : ℕ → D} (run : LoopRun P σ v₀) (hm : Monotone σ.ts)
    (hstrat : ∀ j, Stratified (run.K j) P.secs) (hcf : ∀ j, ConflictFree (run.X j))
    (hLet : LetSem Γ σ v₀) :
    ∀ i, σ.sat i v₀ χ := by
  have hall := run.clauses_hold hstrat hcf hpres
  exact program_sound hwf hV hrw hC hm hLet (fun i c hc => hall i c (hPR c hc))
    (fun i c hc => hall i c (hPC c hc))

end Enfflash
