/-
  Enfflash formalization — main theorems, with the dependency analysis
  discharging the stratification and conflict-freedom hypotheses.
-/
import Enfflash.Conflict
import Enfflash.Tables
import Enfflash.DFG

namespace Enfflash

universe u
variable {B L D : Type u}

/-- **Compilation correctness, with dependency analysis.**  Let `□χ` be in
    let-normal form, `R` a valid realization of its lets, `C` a candidate
    clause set for `χ`, and `P` an EF program containing `C` and the gated
    realization clauses, all with present filters, such that

    * the sections of `P` are ordered along the Event Dependency Graph
      (`rk` is monotone along EDG edges, sections are ordered by `rk`);
    * the conflict checks succeed: cause/suppress pairs of a section are
      exclusive when only events outside the section are shared, and deferred
      causes are exclusive with suppressions without sharing anything;

    then every output of the enforcement loop running `P`, whose tables
    compute the lets, satisfies `□χ`. -/
theorem enforcer_sound_analysed {S : Sig B L D} {Γ : L → Option (LetDef B L D)}
    {R : Real B L D} {r : L → L → Prop} (hwf : WellFounded r) (hV : R.Valid S Γ r)
    {χ : Fm B L D} {CS : List (List (Clause B L D))}
    (hrw : Rw (R.scope S (fun _ => True)) true χ CS) {C : List (Clause B L D)} (hC : C ∈ CS)
    (P : Program B L D) (hPC : ∀ c ∈ C, c ∈ P.rules)
    (hPR : ∀ c, R.clauses S.ar c → c ∈ P.rules)
    (hpres : ∀ c ∈ P.rules, c.trig.filter.present)
    {σ : Tr B L D} {v₀ : ℕ → D} (run : LoopRun P σ v₀) (hm : Monotone σ.ts)
    (htab : TablesComputeLets σ v₀ Γ)
    -- EDG section order
    (ld : L → List (Ev B L)) (hld : ∀ j, LetDeps (run.K j) ld) (rk : Ev B L → ℕ)
    (hrk : ∀ e e', EDG ld P.rules e e' → rk e ≤ rk e') (hord : RankOrdered rk P.secs)
    -- conflict checks
    (hchk : ∀ j, ∀ sec ∈ P.secs, ∀ c₁ ∈ sec, ∀ c₂ ∈ sec,
      ExclusiveNow (run.K j) (effNames sec)ᶜ c₁ c₂)
    (hdef : ∀ c₁ ∈ P.rules, ∀ c₂ ∈ P.rules, ExclusiveDeferred c₁ c₂) :
    ∀ i, σ.sat i v₀ χ :=
  enforcer_sound hwf hV hrw hC P hPC hPR hpres run hm
    (fun j => stratified_of_rank (hld j) rk P.secs hrk hord)
    (run.conflictFree hord.sectionsDisjoint hchk hdef)
    (letSem_of_tables σ v₀ htab)

/-- The same, for the sections computed from the SCCs of the EDG. -/
theorem enforcer_sound_scc {S : Sig B L D} {Γ : L → Option (LetDef B L D)}
    {R : Real B L D} {r : L → L → Prop} (hwf : WellFounded r) (hV : R.Valid S Γ r)
    {χ : Fm B L D} {CS : List (List (Clause B L D))}
    (hrw : Rw (R.scope S (fun _ => True)) true χ CS) {C : List (Clause B L D)} (hC : C ∈ CS)
    (ld : L → List (Ev B L)) (rules : List (Clause B L D))
    (hPC : ∀ c ∈ C, c ∈ rules) (hPR : ∀ c, R.clauses S.ar c → c ∈ rules)
    (hpres : ∀ c ∈ rules, c.trig.filter.present)
    {σ : Tr B L D} {v₀ : ℕ → D} (run : LoopRun ⟨sccSections ld rules⟩ σ v₀)
    (hm : Monotone σ.ts) (htab : TablesComputeLets σ v₀ Γ)
    (hld : ∀ j, LetDeps (run.K j) ld)
    (hchk : ∀ j, ∀ sec ∈ sccSections ld rules, ∀ c₁ ∈ sec, ∀ c₂ ∈ sec,
      ExclusiveNow (run.K j) (effNames sec)ᶜ c₁ c₂)
    (hdef : ∀ c₁ ∈ rules, ∀ c₂ ∈ rules, ExclusiveDeferred c₁ c₂) :
    ∀ i, σ.sat i v₀ χ := by
  have hmem : ∀ c, c ∈ (⟨sccSections ld rules⟩ : Program B L D).rules ↔ c ∈ rules :=
    sccSections_cover ld rules
  refine enforcer_sound_analysed hwf hV hrw hC ⟨sccSections ld rules⟩
    (fun c hc => (hmem c).2 (hPC c hc)) (fun c hc => (hmem c).2 (hPR c hc))
    (fun c hc => hpres c ((hmem c).1 hc)) run hm htab ld hld (Graph.rank (EDG ld rules))
    ?_ (sccSections_rankOrdered ld rules) hchk
    (fun c₁ h₁ c₂ h₂ => hdef c₁ ((hmem c₁).1 h₁) c₂ ((hmem c₂).1 h₂))
  rintro e e' ⟨c, hc, he, rfl⟩
  exact Graph.rank_mono (EDG.finite ld rules) ⟨c, (hmem c).1 hc, he, rfl⟩

/-- **Compilation correctness** for `P = Compile(Γ, R, ≺)` (Algorithm 4):
    the same, for the rules sectioned along any topological order `≺` of the
    SCCs of the EDG (`SCCOrder`). -/
theorem enforcer_sound_topo {S : Sig B L D} {Γ : L → Option (LetDef B L D)}
    {R : Real B L D} {r : L → L → Prop} (hwf : WellFounded r) (hV : R.Valid S Γ r)
    {χ : Fm B L D} {CS : List (List (Clause B L D))}
    (hrw : Rw (R.scope S (fun _ => True)) true χ CS) {C : List (Clause B L D)} (hC : C ∈ CS)
    (ld : L → List (Ev B L)) (rules : List (Clause B L D))
    (hPC : ∀ c ∈ C, c ∈ rules) (hPR : ∀ c, R.clauses S.ar c → c ∈ rules)
    (hpres : ∀ c ∈ rules, c.trig.filter.present)
    {secs : List (List (Clause B L D))} (hord : SCCOrder ld rules secs)
    {σ : Tr B L D} {v₀ : ℕ → D} (run : LoopRun ⟨secs⟩ σ v₀)
    (hm : Monotone σ.ts) (htab : TablesComputeLets σ v₀ Γ)
    (hld : ∀ j, LetDeps (run.K j) ld)
    (hchk : ∀ j, ∀ sec ∈ secs, ∀ c₁ ∈ sec, ∀ c₂ ∈ rules,
      Exclusive (run.K j) (effNames sec)ᶜ c₁ c₂) :
    ∀ i, σ.sat i v₀ χ := by
  have hmem : ∀ c, c ∈ (⟨secs⟩ : Program B L D).rules ↔ c ∈ rules := hord.cover
  obtain ⟨hnow, hdef⟩ := Exclusive.split (K := run.K) (secs := secs)
    fun j sec hs c₁ h₁ c₂ h₂ => hchk j sec hs c₁ h₁ c₂ ((hmem c₂).1 h₂)
  exact enforcer_sound hwf hV hrw hC ⟨secs⟩
    (fun c hc => (hmem c).2 (hPC c hc)) (fun c hc => (hmem c).2 (hPR c hc))
    (fun c hc => hpres c ((hmem c).1 hc)) run hm
    (fun j => stratified_of_topo (hld j) rules secs
      (fun sec hs c hc => (hmem c).1 (List.mem_flatten.2 ⟨sec, hs, hc⟩)) hord.topo)
    (run.conflictFree hord.topo.sectionsDisjoint hnow hdef)
    (letSem_of_tables σ v₀ htab)

end Enfflash
