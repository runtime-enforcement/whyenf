/-
  EnfFlash formalization — realizations of obligation events and the
  soundness of the generated clause program (paper, Sections 4.5 and 4.7).

  A let `p` that is caused (resp. suppressed) somewhere is compiled into the
  obligation event `Cau_p` (resp. `Sup_p`).  The body's clauses are *gated* by
  that obligation event and closed over `p`'s arguments.  The main theorem
  `program_sound` states: on any trace on which all generated clauses hold
  at every time-point, and the lets have their MFOTL meaning, the enforced
  formula holds at every time-point.
-/
import Enfflash.Rewrite

namespace Enfflash

universe u
variable {B L D : Type u}

/-! ## Gating -/

/-- The variables `n, …, n+k-1` (the arguments of a let under `n` locals). -/
def argVars (n k : ℕ) : List (Term D) := (List.range k).map (fun j => .var (n + j))

theorem eval_argVars (ds as : List D) (v : ℕ → D) :
    (argVars ds.length as.length).map (Term.eval (vapp (ds ++ as) v)) = as := by
  apply List.ext_getElem (by simp [argVars])
  intro j h1 h2
  simp only [argVars, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply,
    Term.eval, vapp_append]
  rw [show ds.length + j = j + ds.length by omega, vapp_ge, vapp_lt _ _ _ h2]

/-- Gate a clause (in the context of the let's `k` arguments) by the
    obligation event `o`, closing it over the arguments. -/
def gate (o : Ev B L) (k : ℕ) (c : Clause B L D) : Clause B L D :=
  ⟨c.nloc + k, ⟨c.trig.guards.addAtom (.pred (.ev o) (argVars c.nloc k)), c.trig.filter⟩, c.eff⟩

theorem gate_holds {σ : Tr B L D} {i : ℕ} {v : ℕ → D} {o : Ev B L} {k : ℕ}
    {c : Clause B L D} (h : (gate o k c).holds σ i v) (as : List D) (hk : as.length = k)
    (hin : (o, as) ∈ σ.db i) : c.holds σ i (vapp as v) := by
  intro ds hds htr
  have := h (ds ++ as) (by simp [gate, hds, hk])
  rw [vapp_append] at this
  apply this
  refine ⟨(Guards.sat_addAtom _ _ _ _ _).2 ⟨?_, ?_⟩, ?_⟩
  · exact htr.1
  · simp only [GAtom.sat, Tr.prIn]
    rw [← vapp_append, ← hds, ← hk, eval_argVars]; exact hin
  · exact htr.2

/-! ## Realizations -/

/-- The chosen clause set realizing each let's causation and suppression
    (the output of `Realizations`, in the let's argument context). -/
structure Real (B L D : Type u) where
  cauCl : L → Option (List (Clause B L D))
  supCl : L → Option (List (Clause B L D))

namespace Real

/-- All gated realization clauses. -/
def clauses (R : Real B L D) (ar : L → ℕ) (c : Clause B L D) : Prop :=
  (∃ p C, R.cauCl p = some C ∧ ∃ c₀ ∈ C, c = gate (.cau p) (ar p) c₀) ∨
  (∃ p C, R.supCl p = some C ∧ ∃ c₀ ∈ C, c = gate (.sup p) (ar p) c₀)

/-- The rewriting signature in which lets satisfying `r · p` may be used. -/
def scope (R : Real B L D) (S : Sig B L D) (ok : L → Prop) : Sig B L D :=
  { S with okC := fun q => ok q ∧ R.cauCl q ≠ none, okS := fun q => ok q ∧ R.supCl q ≠ none }

/-- A realization is valid if each chosen clause set is derived (in the scope
    of strictly earlier lets) from the causation/suppression target of the
    let's body. -/
structure Valid (R : Real B L D) (S : Sig B L D) (Γ : L → Option (LetDef B L D))
    (r : L → L → Prop) : Prop where
  cau : ∀ p C, R.cauCl p = some C → ∃ d φ CS, Γ p = some d ∧ d.arity = S.ar p ∧
    d.body.cauTarget = some φ ∧ Rw (R.scope S (r · p)) true φ CS ∧ C ∈ CS
  sup : ∀ p C, R.supCl p = some C → ∃ d φ CS, Γ p = some d ∧ d.arity = S.ar p ∧
    d.body.supTarget = some φ ∧ Rw (R.scope S (r · p)) false φ CS ∧ C ∈ CS

end Real

/-- Obligation events are sound: whenever `Cau_p(ā)` (resp. `Sup_p(ā)`) is in
    the trace, `p(ā)` holds (resp. fails). -/
theorem obligations_sound {S : Sig B L D} {Γ : L → Option (LetDef B L D)} {R : Real B L D}
    {r : L → L → Prop} (hwf : WellFounded r) (hV : R.Valid S Γ r)
    {σ : Tr B L D} {v₀ : ℕ → D} (hm : Monotone σ.ts) (hLet : LetSem Γ σ v₀)
    (hR : ∀ i c, R.clauses S.ar c → c.holds σ i v₀) :
    ∀ p, (R.cauCl p ≠ none → CauOK σ S.ar p) ∧ (R.supCl p ≠ none → SupOK σ S.ar p) := by
  intro p
  induction p using hwf.induction with
  | _ p ih =>
  have hC : ∀ q, (R.scope S (r · p)).okC q → CauOK σ (R.scope S (r · p)).ar q :=
    fun q hq => (ih q hq.1).1 hq.2
  have hS : ∀ q, (R.scope S (r · p)).okS q → SupOK σ (R.scope S (r · p)).ar q :=
    fun q hq => (ih q hq.1).2 hq.2
  constructor
  · intro hp i as hlen hin
    obtain ⟨C, hCp⟩ := Option.ne_none_iff_exists'.1 hp
    obtain ⟨d, φ, CS, hd, har, ht, hrw, hCS⟩ := hV.cau p C hCp
    have hCh : Clauses.holds σ i (vapp as v₀) C := fun c hc =>
      gate_holds (hR i _ (Or.inl ⟨p, C, hCp, c, hc, rfl⟩)) as hlen hin
    have hsat := hrw.sound hm hC hS C hCS i _ hCh
    simp only [polSem, if_true] at hsat
    have hsem := LBody.cauTarget_sound σ i _ ht hsat
    exact (hLet p d hd i as (hlen.trans har.symm)).2 hsem
  · intro hp i as hlen hin hlv
    obtain ⟨C, hCp⟩ := Option.ne_none_iff_exists'.1 hp
    obtain ⟨d, φ, CS, hd, har, ht, hrw, hCS⟩ := hV.sup p C hCp
    have hCh : Clauses.holds σ i (vapp as v₀) C := fun c hc =>
      gate_holds (hR i _ (Or.inr ⟨p, C, hCp, c, hc, rfl⟩)) as hlen hin
    have hsat := hrw.sound hm hC hS C hCS i _ hCh
    simp only [polSem, Bool.false_eq_true, if_false] at hsat
    have hsem := LBody.supTarget_sound σ i _ ht hsat
    exact hsem ((hLet p d hd i as (hlen.trans har.symm)).1 hlv)

/-- **Soundness of the generated clause program.**  Let `□χ` be in
    let-normal form with lets `Γ`, `R` a valid realization, and `C` a
    candidate clause set for `χ`.  On every trace with monotone timestamps
    where the lets have their MFOTL meaning and every clause of the program
    (`C` together with the gated realizations) holds at every time-point, `χ`
    holds at every time-point, i.e. `□χ` holds. -/
theorem program_sound {S : Sig B L D} {Γ : L → Option (LetDef B L D)} {R : Real B L D}
    {r : L → L → Prop} (hwf : WellFounded r) (hV : R.Valid S Γ r)
    {χ : Fm B L D} {CS : List (List (Clause B L D))}
    (hrw : Rw (R.scope S (fun _ => True)) true χ CS) {C : List (Clause B L D)} (hC : C ∈ CS)
    {σ : Tr B L D} {v₀ : ℕ → D} (hm : Monotone σ.ts) (hLet : LetSem Γ σ v₀)
    (hR : ∀ i c, R.clauses S.ar c → c.holds σ i v₀) (hCh : ∀ i, Clauses.holds σ i v₀ C) :
    ∀ i, σ.sat i v₀ χ := by
  have hob := obligations_sound hwf hV hm hLet hR
  intro i
  have hC' : ∀ q, (R.scope S (fun _ => True)).okC q → CauOK σ (R.scope S (fun _ => True)).ar q :=
    fun q hq => (hob q).1 hq.2
  have hS' : ∀ q, (R.scope S (fun _ => True)).okS q → SupOK σ (R.scope S (fun _ => True)).ar q :=
    fun q hq => (hob q).2 hq.2
  have := hrw.sound hm hC' hS' C hC i v₀ (hCh i)
  simpa [polSem] using this

end Enfflash
