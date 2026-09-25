/-
  Enfflash formalization — the paper's claims, in paper order.

  Every numbered lemma and theorem of the paper (except the complexity
  results of Section 3.3) is restated here in the paper's vocabulary and
  proved by the corresponding theorem of the development.  `PAPER.md` maps
  the paper's definitions to their Lean counterparts.
-/
import Enfflash.EndToEnd
import Enfflash.TypeSystem
import Enfflash.Examples

namespace Enfflash.Paper

open Enfflash

variable {B L D : Type}

/-! ## Section 2.3: enforcers -/

/-- *An enforcer `ℰ` is sound w.r.t. `□φ` if every modified trace `ℰ(σ)`
    complies with `□φ`.*  (`SoundEnforcer`, unfolded.) -/
theorem sound_enforcer_def (φ : MF B D) (v₀ : ℕ → D) (E : InputTrace B D → Tr B ℕ D) :
    SoundEnforcer φ v₀ E ↔ ∀ ρ i, φ.sat (E ρ) [] i v₀ := Iff.rfl

/-! ## Section 3.2: semantics of EF -/

/-- *`Saturate` runs a `fixpoint` section until a pass leaves `(Ω, C, S)`
    unchanged*: this happens exactly at a fixpoint of the section's rules. -/
theorem saturate_until_unchanged (K : Ctx B L D) (D₀ : DB B L D)
    (sec : List (Clause B L D)) (X : Set (Act B L D)) :
    step K D₀ sec X = X ↔ Fixed K D₀ sec X :=
  step_eq_iff_fixed K D₀ sec X

/-! ## Section 4.1: let-normal form -/

/-- **Theorem 4.1.**  *For any formula `□φ` in MFOTL, there exists a
    semantically equivalent formula in let-normal form*: lets `Γ` and a
    formula `χ` in let-normal form (`LNF`) such that `χ` holds exactly where
    `φ` does on every trace interpreting the lets by `Γ` (`LetEquiv`). -/
theorem thm_4_1 (φ : MF B D) (hφ : φ.WF []) :
    ∃ Γ χ, LNF Γ χ ∧ LetEquiv φ Γ χ :=
  ⟨_, _, let_normal_form φ hφ⟩

/-! ## Section 4.2: guard extraction -/

/-- **Lemma 4.2.**  *If `m ⊢ (π, φ) ↝⁺_x (π', φ')`, then `x` is bound in
    every `κ' ∈ π'` and `⋁π ∧ φ ≡ ⋁π' ∧ φ'`.* -/
theorem lem_4_2 {m : Pr B L → Prop} {x : ℕ} {π π' : Guards B L D} {φ φ' : Fm B L D}
    (h : GX m x true π φ π' φ') :
    π'.bindsAll x ∧ GEquiv true π φ π' φ' :=
  ⟨h.sound.2, h.sound.1⟩

/-- **Lemma 4.3.**  *If `Guards^m_X(Φ) = (π, φ)`, then every `κ ∈ π` binds
    every `x ∈ X`, and `⋁π ∧ φ ≡ Φ`.* -/
theorem lem_4_3 {m : Pr B L → Prop} {X : List ℕ} {Φ φ : Fm B L D} {π : Guards B L D}
    (h : GXJ m X true Φ π φ) :
    (∀ x ∈ X, π.bindsAll x) ∧ GEquiv true [[]] Φ π φ :=
  ⟨h.sound.2, h.sound.1⟩

/-! ## Section 4.5: dependency analysis -/

/-- *Cause/suppress conflicts.*  If every rule of a section passes the
    conflict check against every rule (`Exclusive`: an instance caused by the
    first is never suppressed by the second; for an immediate cause on working
    sets agreeing on the events not acted upon by the section, for a deferred
    cause without sharing anything), and the sections act on disjoint events,
    then no output time-point both causes and suppresses an event. -/
theorem conflict_check_sound {P : Program B L D} {σ : Tr B L D} {v₀ : ℕ → D}
    (R : LoopRun P σ v₀) (hd : SectionsDisjoint P.secs)
    (hchk : ∀ j, ∀ sec ∈ P.secs, ∀ c₁ ∈ sec, ∀ c₂ ∈ P.rules,
      Exclusive (R.K j) (effNames sec)ᶜ c₁ c₂) :
    ∀ j, ConflictFree (R.X j) :=
  let h := Exclusive.split (K := R.K) hchk
  R.conflictFree hd h.1 h.2

/-- *Termination.*  If no non-stable edge of a section's data-flow graph lies
    on a cycle (`DFGAcyclic`; edges through non-stable function terms and
    through aggregations are non-stable), the section reaches its fixpoint
    after finitely many passes (with finitely many actions), from any finite
    input. -/
theorem termination {K : Ctx B L D} {D₀ : DB B L D} {sec : List (Clause B L D)}
    {Stab : Set D → Set D} (hS : StabOp Stab) {A : Set D → Set D} (hA : CloOp A)
    {V : Set D} (hV : V.Finite) (hD : D₀.Finite)
    {lsrc nsrc : L → ℕ → List (Pos B L)} {ok : L → Prop} (hK : LetsFlow K V lsrc nsrc A ok)
    (hc : ∀ c ∈ sec, DFClause V K.v₀ ok c) (hacyc : DFGAcyclic lsrc nsrc Stab sec)
    {X₀ : Set (Act B L D)} (hX₀ : X₀.Finite) :
    ∃ n, Fixed K D₀ sec ((step K D₀ sec)^[n] X₀) ∧ ((step K D₀ sec)^[n] X₀).Finite :=
  dfg_terminates K D₀ sec hS hA V hV hD lsrc nsrc ok hK hc hacyc X₀ hX₀

/-- *Sections in a topological order of the SCCs of the EDG are
    stratified*: no rule of a later section acts on an event read by a rule
    of an earlier one. -/
theorem topological_order_stratified {K : Ctx B L D} {ld : L → List (Ev B L)}
    (hK : LetDeps K ld) {rules : List (Clause B L D)} {secs : List (List (Clause B L D))}
    (h : SCCOrder ld rules secs) : Stratified K secs :=
  stratified_of_topo hK rules secs
    (fun sec hs c hc => (h.cover c).1 (List.mem_flatten.2 ⟨sec, hs, hc⟩)) h.topo

/-- A topological order of the SCCs exists. -/
theorem scc_order_exists (ld : L → List (Ev B L)) (rules : List (Clause B L D)) :
    ∃ secs, SCCOrder ld rules secs :=
  ⟨_, sccOrder_spec ld rules⟩

/-! ## Section 4.6: compilation -/

/-- **Theorem 4.5 (Compilation correctness).**  *Let `R` be a candidate
    clause set accepted by the two checks of Section 4.5 and
    `P = Compile(Γ, R, ≺)`.  Then `P` is a sound enforcer for `□φ`.* -/
theorem thm_4_5 {Φ : Policy B D} (P : Compiled Φ) (h : P.Checks) :
    SoundEnforcer Φ.φ P.v₀ (enforce P h) :=
  enforcement_correct P h

/-! ## Appendix A: a type system for the enforceable fragment -/

/-- **Lemma A.1 (1).**  *`m ⊢ (π, ψ) ↝^p_x (π', ψ')` holds for some
    `(π', ψ')` iff every `κ ∈ π` binds `x` or `ψ : GRD(x)^p`.* -/
theorem lem_A_1_1 {m : Pr B L → Prop} {x : ℕ} {p : Bool} {π : Guards B L D} {ψ : Fm B L D} :
    (∃ π' ψ', GX m x p π ψ π' ψ') ↔ (π.bindsAll x ∨ Grd m x p ψ) :=
  gx_iff

/-- **Lemma A.1 (2).**  *`Guards^m_X(Φ) ≠ ⊥` iff `Φ : 𝔾⁺_X`.* -/
theorem lem_A_1_2 {m : Pr B L → Prop} {X : List ℕ} {Φ : Fm B L D} :
    (∃ π φ, GXJ m X true Φ π φ) ↔ Enum m X true Φ :=
  gxj_iff

/-- **Definition A.2 (EF-MFOTL).**  *`□φ` is in EF-MFOTL with clause set `Δ`
    if its let-normal form, with lets typed by some context `Γ`, satisfies
    `Γ ⊢ χ : ℂ ▷ Δ`.* -/
theorem def_A_2 (S₀ : Sig B ℕ D) (φ : MF B D) (Δ : List (Clause B ℕ D)) :
    EFMFOTL S₀ φ Δ ↔ ∃ κ : Caps, TypedLets S₀ (lnf φ).2 κ ∧
      Typ (sigOf S₀ (enumCaps κ) κ.C κ.S) true (lnf φ).1 Δ := Iff.rfl

/-- **Theorem A.3.**  *`□φ` is in EF-MFOTL with clause set `Δ` iff the
    compilation of Section 4 succeeds on `□φ` with candidate clause set
    `Δ`.* -/
theorem thm_A_3 (S₀ : Sig B ℕ D) (φ : MF B D) (Δ : List (Clause B ℕ D)) :
    EFMFOTL S₀ φ Δ ↔ Nonempty (Compilation S₀ φ Δ) :=
  efmfotl_iff_compiles S₀ φ Δ

/-- **Example A.4.**  *`φ_del` has let-normal form `□¬∃d,u. φ₀` and
    `Γ ⊢ ¬∃d,u. φ₀ : ℂ ▷ {(deletion_request(d,u), ⊤) ⇒ ◇_[30,30] delete(d,u)}`*;
    hence (Theorem A.3) its compilation succeeds with this clause set. -/
theorem ex_A_4 :
    EFMFOTL Examples.S₀ Examples.phiDel [Examples.delRule] ∧
      Compiles Examples.S₀ Examples.phiDel [Examples.delRule] :=
  ⟨Examples.phiDel_efmfotl, Examples.phiDel_compiles⟩

end Enfflash.Paper
