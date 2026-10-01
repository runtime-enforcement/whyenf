/-
  Enfflash formalization — finite directed graphs.

  * `rank`: the number of ancestors of a node.  It is monotone along edges,
    and an edge between nodes of equal rank lies inside a strongly connected
    component.  Grouping nodes by rank thus yields a topological order of
    the SCCs (possibly merging independent SCCs).
  * `level`: the number of *strict* edges upstream of a node.  If no strict
    edge lies on a cycle, it is monotone along edges and strictly increases
    along strict edges.
-/
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finite.Prod

namespace Enfflash.Graph

variable {α : Type*} (E : α → α → Prop)

open Relation

/-- The graph's nodes (all edge endpoints) lie in a finite set. -/
def FiniteGraph : Prop := ∃ N : Set α, N.Finite ∧ ∀ x y, E x y → x ∈ N ∧ y ∈ N

/-- Ancestors of `y` (including `y`). -/
def anc (y : α) : Set α := {z | ReflTransGen E z y}

/-- The rank of a node: its number of ancestors. -/
noncomputable def rank (y : α) : ℕ := (anc E y).ncard

variable {E}

theorem anc_finite (hE : FiniteGraph E) (y : α) : (anc E y).Finite := by
  obtain ⟨N, hN, hEN⟩ := hE
  refine (hN.insert y).subset ?_
  intro z hz
  rcases ReflTransGen.cases_head hz with rfl | ⟨w, hzw, -⟩
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ (hEN _ _ hzw).1

theorem anc_mono_path {x y : α} (h : ReflTransGen E x y) : anc E x ⊆ anc E y :=
  fun _ hz => hz.trans h

/-- The rank is monotone along paths. -/
theorem rank_mono_path (hE : FiniteGraph E) {x y : α} (h : ReflTransGen E x y) :
    rank E x ≤ rank E y :=
  Set.ncard_le_ncard (anc_mono_path h) (anc_finite hE y)

/-- A path between nodes of equal rank lies on a cycle (in an SCC). -/
theorem rank_eq_path (hE : FiniteGraph E) {x y : α} (h : ReflTransGen E x y)
    (heq : rank E x = rank E y) : ReflTransGen E y x := by
  have hs : anc E x = anc E y :=
    Set.eq_of_subset_of_ncard_le (anc_mono_path h) heq.ge (anc_finite hE y)
  have hy : y ∈ anc E y := ReflTransGen.refl
  rw [← hs] at hy
  exact hy

/-! ### Levels w.r.t. strict edges -/

variable (E) (S : α → α → Prop)

/-- Strict edges upstream of `y`. -/
def up (y : α) : Set (α × α) := {p | S p.1 p.2 ∧ ReflTransGen E p.2 y}

/-- The level of `y`: the number of strict edges upstream of it. -/
noncomputable def level (y : α) : ℕ := (up E S y).ncard

variable {E S}

theorem strict_finite (hE : FiniteGraph E) (hSE : ∀ x y, S x y → E x y) :
    {p : α × α | S p.1 p.2}.Finite := by
  obtain ⟨N, hN, hEN⟩ := hE
  exact (hN.prod hN).subset fun p hp => ⟨(hEN _ _ (hSE _ _ hp)).1, (hEN _ _ (hSE _ _ hp)).2⟩

theorem level_mono (hE : FiniteGraph E) (hSE : ∀ x y, S x y → E x y) {x y : α} (h : E x y) :
    level E S x ≤ level E S y :=
  Set.ncard_le_ncard (fun _ hp => ⟨hp.1, ReflTransGen.tail hp.2 h⟩)
    ((strict_finite hE hSE).subset fun _ hp => hp.1)

/-- If no strict edge lies on a cycle, the level strictly increases along
    strict edges. -/
theorem level_strict (hE : FiniteGraph E) (hSE : ∀ x y, S x y → E x y)
    (hacyc : ∀ x y, S x y → ¬ ReflTransGen E y x) {x y : α} (h : S x y) :
    level E S x < level E S y := by
  have hsub : up E S x ⊆ up E S y := fun p hp => ⟨hp.1, ReflTransGen.tail hp.2 (hSE _ _ h)⟩
  have hin : (x, y) ∈ up E S y := ⟨h, ReflTransGen.refl⟩
  have hnin : (x, y) ∉ up E S x := fun hp => hacyc x y h hp.2
  exact Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.2 ⟨hsub, fun he => hnin (he ▸ hin)⟩)
    ((strict_finite hE hSE).subset fun _ hp => hp.1)

theorem level_le (hE : FiniteGraph E) (hSE : ∀ x y, S x y → E x y) (y : α) :
    level E S y ≤ {p : α × α | S p.1 p.2}.ncard :=
  Set.ncard_le_ncard (fun _ hp => hp.1) (strict_finite hE hSE)

end Enfflash.Graph
