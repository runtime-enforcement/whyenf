/-
  Proof of the closure property of stable function symbols (§4.5).
-/
import Paper.Claims
import Paper.Dependency

namespace Paper

variable {Voc : Vocabulary}

theorem closure_finite (O : StabOrder Voc) {F : Set Voc.𝔽} (hF : ∀ f ∈ F, Stable O f)
    {V : Set Voc.𝔻} (hV : V.Finite) : {d | Closure F V d}.Finite := by
  have key : ∀ d, Closure F V d → ∃ v ∈ V, d = v ∨ O.le d v := by
    intro d h
    induction h with
    | base hd => exact ⟨_, hd, Or.inl rfl⟩
    | @app f a hf _ ih =>
      obtain ⟨k, hk⟩ := hF f hf a
      obtain ⟨v, hv, h | h⟩ := ih k
      · exact ⟨v, hv, Or.inr (h ▸ hk)⟩
      · exact ⟨v, hv, Or.inr (O.trans _ _ _ hk h)⟩
  refine (hV.union (hV.biUnion fun v _ => O.finDown v)).subset fun d hd => ?_
  obtain ⟨v, hv, h | h⟩ := key d hd
  · exact Or.inl (h ▸ hv)
  · exact Or.inr (Set.mem_biUnion hv h)

theorem claim_closure_finite : Claim_closure_finite Voc := fun O _ hF _ hV => closure_finite O hF hV

end Paper
