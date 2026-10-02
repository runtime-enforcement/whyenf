/-
  Levels of a finite graph w.r.t. a set of strict edges, and value bounds.
  (Adapted from the legacy formalization, `lean/Enfflash/Graph.lean`.)
-/
import Paper.Proof.Conflict

namespace Paper

namespace Graph

variable {α : Type} (E : α → α → Prop)

open Relation

/-- The graph's nodes (all edge endpoints) lie in a finite set. -/
def FiniteGraph : Prop := ∃ N : Set α, N.Finite ∧ ∀ x y, E x y → x ∈ N ∧ y ∈ N

variable (S : α → α → Prop)

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

theorem level_strict (hE : FiniteGraph E) (hSE : ∀ x y, S x y → E x y)
    (hacyc : ∀ x y, S x y → ¬ ReflTransGen E y x) {x y : α} (h : S x y) :
    level E S x < level E S y := by
  have hsub : up E S x ⊆ up E S y := fun p hp => ⟨hp.1, ReflTransGen.tail hp.2 (hSE _ _ h)⟩
  have hin : (x, y) ∈ up E S y := ⟨h, ReflTransGen.refl⟩
  have hnin : (x, y) ∉ up E S x := fun hp => hacyc x y h hp.2
  exact Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.2 ⟨hsub, fun he => hnin (he ▸ hin)⟩)
    ((strict_finite hE hSE).subset fun _ hp => hp.1)

end Graph

/-! ## Value bounds -/

variable {Voc : Vocabulary}

/-- `X` together with everything below it. -/
def Dn (O : StabOrder Voc) (X : Set Voc.𝔻) : Set Voc.𝔻 := X ∪ {d | ∃ x ∈ X, O.le d x}

theorem Dn_finite (O : StabOrder Voc) {X : Set Voc.𝔻} (h : X.Finite) : (Dn O X).Finite :=
  h.union ((h.biUnion fun x _ => O.finDown x).subset fun d ⟨x, hx, hd⟩ => Set.mem_biUnion hx hd)

theorem Dn_down (O : StabOrder Voc) {X : Set Voc.𝔻} {d d' : Voc.𝔻} (h : d ∈ Dn O X)
    (h' : O.le d' d) : d' ∈ Dn O X := by
  rcases h with h | ⟨x, hx, hd⟩
  · exact Or.inr ⟨d, h, h'⟩
  · exact Or.inr ⟨x, hx, O.trans _ _ _ h' hd⟩

theorem sub_Dn (O : StabOrder Voc) (X : Set Voc.𝔻) : X ⊆ Dn O X := Set.subset_union_left

/-- The value bounds by level: `W 0 = ↓B`, `W (n+1) = ↓(W n ∪ Φ(W n))`. -/
def Wb (O : StabOrder Voc) (B : Set Voc.𝔻) (Φ : Set Voc.𝔻 → Set Voc.𝔻) : ℕ → Set Voc.𝔻
  | 0 => Dn O B
  | n + 1 => Dn O (Wb O B Φ n ∪ Φ (Wb O B Φ n))

section
variable (O : StabOrder Voc) (B : Set Voc.𝔻) (Φ : Set Voc.𝔻 → Set Voc.𝔻)

theorem Wb_finite (hB : B.Finite) (hΦ : ∀ X, X.Finite → (Φ X).Finite) : ∀ n, (Wb O B Φ n).Finite
  | 0 => Dn_finite O hB
  | n + 1 => Dn_finite O ((Wb_finite hB hΦ n).union (hΦ _ (Wb_finite hB hΦ n)))

theorem Wb_succ_sub (n : ℕ) : Wb O B Φ n ⊆ Wb O B Φ (n + 1) :=
  fun d hd => sub_Dn O _ (Or.inl hd)

theorem Wb_mono {n m : ℕ} (h : n ≤ m) : Wb O B Φ n ⊆ Wb O B Φ m := by
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact le_rfl
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact (ih (by omega)).trans (Wb_succ_sub O B Φ m)
    · subst h; exact le_rfl

theorem Wb_base (n : ℕ) : B ⊆ Wb O B Φ n :=
  (sub_Dn O B).trans (Wb_mono O B Φ (Nat.zero_le n))

theorem Wb_down {n : ℕ} {d d' : Voc.𝔻} (h : d ∈ Wb O B Φ n) (h' : O.le d' d) : d' ∈ Wb O B Φ n := by
  cases n with
  | zero => exact Dn_down O h h'
  | succ n => exact Dn_down O h h'

theorem Wb_Φ (n : ℕ) : Φ (Wb O B Φ n) ⊆ Wb O B Φ (n + 1) :=
  fun d hd => sub_Dn O _ (Or.inr hd)

end

end Paper
