/-
  EnfFlash formalization — values of working sets and actions, used by the
  termination argument (`DFG.lean`): the active domain, the arguments of
  actions, and finiteness of lists over a finite set.
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

end Enfflash
