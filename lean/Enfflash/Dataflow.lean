/-
  Enfflash formalization — termination of fixpoint sections (paper,
  Section 4.5, "Termination").

  If all effect arguments of a section are *stable* (constants, context
  variables, or local variables bound by every guard), rules can only copy
  values that are already present.  All actions then range over a finite
  universe and the section reaches its fixpoint after finitely many passes.
  (This is the data-flow criterion of the paper in the case where the
  section's data-flow graph has no non-stable edge.)
-/
import Enfflash.Saturate
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finite.Prod

namespace Enfflash

universe u
variable {B L D : Type u}

/-- The active domain of a database. -/
def adom (W : DB B L D) : Set D := {d | ∃ x ∈ W, d ∈ x.2}

def Act.args : Act B L D → List D
  | cau x | sup x | later _ x | next _ _ x => x.2

/-- Values occurring in (the arguments of) a set of actions. -/
def actDom (X : Set (Act B L D)) : Set D := {d | ∃ a ∈ X, d ∈ a.args}

/-- Replace the arguments of an effect by ground values. -/
def Effect.withArgs (as : List D) : Effect B L D → Act B L D
  | .cau e _ => .cau (e, as)
  | .sup e _ => .sup (e, as)
  | .later b e _ => .later b (e, as)
  | .next n t e _ => .next n t (e, as)

theorem Effect.act_eq_withArgs (w : ℕ → D) (ε : Effect B L D) :
    ε.act w = ε.withArgs (ε.args.map (Term.eval w)) := by
  cases ε <;> rfl

theorem Effect.withArgs_args (as : List D) (ε : Effect B L D) : (ε.withArgs as).args = as := by
  cases ε <;> rfl

/-- A clause is stable w.r.t. the value set `V` and context `v₀`. -/
structure StableClause (V : Set D) (v₀ : ℕ → D) (c : Clause B L D) : Prop where
  args : ∀ t ∈ c.eff.args, (∃ d ∈ V, t = .const d) ∨
    (∃ n, t = .var n ∧ ((c.nloc ≤ n ∧ v₀ (n - c.nloc) ∈ V) ∨ c.trig.guards.bindsAll n))
  eqs : ∀ κ ∈ c.trig.guards, ∀ a ∈ κ, ∀ t d, a = .eq t d → d ∈ V

/-- Lets used in guards only produce known values. -/
def LetsClosed (K : Ctx B L D) (V : Set D) : Prop :=
  ∀ W p as, K.lv W p as → ∀ d ∈ as, d ∈ V ∪ adom W

theorem fires_args {K : Ctx B L D} {V : Set D} (hK : LetsClosed K V) {W : DB B L D}
    {c : Clause B L D} (hc : StableClause V K.v₀ c) {a : Act B L D} (h : fires K W c a) :
    ∀ d ∈ a.args, d ∈ V ∪ adom W := by
  obtain ⟨ds, hds, htr, rfl⟩ := h
  rw [Effect.act_eq_withArgs, Effect.withArgs_args]
  intro d hd
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hd
  rcases hc.args t ht with ⟨d, hdV, rfl⟩ | ⟨n, rfl, (⟨hn, hv⟩ | hb)⟩
  · exact Or.inl hdV
  · left
    simp only [Term.eval]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + c.nloc := ⟨n - c.nloc, by omega⟩
    rw [← hds, vapp_ge]; simpa using hv
  · obtain ⟨κ, hκ, hall⟩ := htr.1
    obtain ⟨g, hg, hbind⟩ := hb κ hκ
    have hgs := hall g hg
    cases g with
    | pred p ts =>
      simp only [GAtom.binds] at hbind
      have hmem : Term.eval (vapp ds K.v₀) (.var n) ∈ ts.map (Term.eval (vapp ds K.v₀)) :=
        List.mem_map_of_mem hbind
      cases p with
      | ev e => exact Or.inr ⟨_, hgs, hmem⟩
      | lp p => exact hK W p _ hgs _ hmem
    | eq t d =>
      simp only [GAtom.binds] at hbind
      subst hbind
      have hdV := hc.eqs κ hκ _ hg _ _ rfl
      simp only [GAtom.sat, Term.eval] at hgs
      simp only [Term.eval]; rw [hgs]; exact Or.inl hdV

theorem adom_work (D₀ : DB B L D) (X : Set (Act B L D)) :
    adom (work D₀ X) ⊆ adom D₀ ∪ actDom X := by
  rintro d ⟨x, (⟨hx, -⟩ | hx), hd⟩
  · exact Or.inl ⟨x, hx, hd⟩
  · exact Or.inr ⟨_, hx, hd⟩

theorem finite_lists (V : Set D) (hV : V.Finite) :
    ∀ k, {as : List D | as.length = k ∧ ∀ d ∈ as, d ∈ V}.Finite
  | 0 => (Set.finite_singleton []).subset (by
      rintro as ⟨h, -⟩; simp [List.eq_nil_of_length_eq_zero h])
  | k + 1 => by
    refine ((hV.prod (finite_lists V hV k)).image (fun p => p.1 :: p.2)).subset ?_
    rintro (_ | ⟨d, as⟩) ⟨hl, hall⟩
    · simp at hl
    · exact ⟨(d, as), ⟨hall d (by simp), by simpa using hl,
        fun x hx => hall x (by simp [hx])⟩, rfl⟩

/-- **Termination of fixpoint sections.**  For a section whose rules are all
    stable, iterating the section from a finite set of initial actions on a
    finite input database reaches a fixpoint after finitely many passes. -/
theorem stable_terminates (K : Ctx B L D) (D₀ : DB B L D) (sec : List (Clause B L D))
    (V : Set D) (hV : V.Finite) (hD : D₀.Finite)
    (hK : LetsClosed K V) (hs : ∀ c ∈ sec, StableClause V K.v₀ c)
    (X₀ : Set (Act B L D)) (hX₀ : X₀.Finite) :
    ∃ n, Fixed K D₀ sec ((step K D₀ sec)^[n] X₀) := by
  -- all values: known constants, input values, and values of initial actions
  set V' := V ∪ adom D₀ ∪ actDom X₀ with hV'
  have hadom : (adom D₀).Finite := by
    have : adom D₀ = ⋃ x ∈ D₀, {d | d ∈ x.2} := by
      ext d; simp [adom]
    rw [this]
    exact hD.biUnion (fun x _ => (List.finite_toSet x.2))
  have hact : (actDom X₀).Finite := by
    have : actDom X₀ = ⋃ a ∈ X₀, {d | d ∈ a.args} := by
      ext d; simp [actDom]
    rw [this]
    exact hX₀.biUnion (fun a _ => (List.finite_toSet a.args))
  have hV'fin : V'.Finite := (hV.union hadom).union hact
  -- the universe of actions
  set U : Set (Act B L D) := X₀ ∪ ⋃ c ∈ sec,
    (fun as => c.eff.withArgs as) '' {as | as.length = c.eff.args.length ∧ ∀ d ∈ as, d ∈ V'}
  have hU : U.Finite := hX₀.union (Set.Finite.biUnion (List.finite_toSet sec)
    (fun c _ => (finite_lists V' hV'fin _).image _))
  have hclosed : ∀ Y ⊆ U, ∀ c ∈ sec, ∀ a, fires K (work D₀ Y) c a → a ∈ U := by
    intro Y hY c hc a ha
    have hargs := fires_args hK (hs c hc) ha
    right
    refine Set.mem_biUnion hc ?_
    obtain ⟨ds, -, -, rfl⟩ := ha
    refine ⟨_, ⟨by simp, fun d hd => ?_⟩, (Effect.act_eq_withArgs _ _).symm⟩
    have hd' : d ∈ (c.eff.act (vapp ds K.v₀)).args := by
      rw [Effect.act_eq_withArgs, Effect.withArgs_args]; exact hd
    rcases hargs d hd' with h | h
    · exact Or.inl (Or.inl h)
    · rcases adom_work D₀ Y h with h | ⟨b, hb, hdb⟩
      · exact Or.inl (Or.inr h)
      · rcases hY hb with hb | hb
        · exact Or.inr ⟨b, hb, hdb⟩
        · rw [Set.mem_iUnion₂] at hb
          obtain ⟨c', hc', as, ⟨-, hall⟩, rfl⟩ := hb
          rw [Effect.withArgs_args] at hdb
          exact hall d hdb
  obtain ⟨n, -, hn, -⟩ := fixpoint_exists K D₀ sec U hU X₀ Set.subset_union_left hclosed
  exact ⟨n, hn⟩

end Enfflash
