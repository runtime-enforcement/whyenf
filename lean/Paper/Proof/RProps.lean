/-
  Properties of all clauses of `R`.
-/
import Paper.Proof.RTyped

namespace Paper

open Classical

variable {Voc : Vocabulary}

namespace Setup
variable (U : Setup Voc)

theorem typed_hyps (Γ : LetCtx Voc) (hΓ : ∀ e, (Γ e).isSome → IsLet U.L.lets e) :
    ∀ {α φ 𝒞}, Rw U.Ξ Γ α φ 𝒞 → TypedP U.L.lets φ 𝒞 := by
  intro α φ 𝒞 h
  refine typed_rw hΓ (fun e ⟨d, hd, he⟩ => ?_) (fun e ⟨d, hd, he⟩ => ?_) h
  · subst he; exact ⟨(U.wf.fresh_let d hd).1, (U.wf.fresh_let d hd).2.1⟩
  · subst he
    exact ⟨(U.wf.obl_arity d hd).1, (U.wf.obl_arity d hd).2,
      (U.wf.obl_fresh d.e _ (Set.mem_insert _ _)).1, (U.wf.obl_fresh d.e _ (Set.mem_insert_of_mem _ rfl)).1⟩

/-- **Every clause of `R`** has a well-typed effect on a non-let event and is
    guarded. -/
theorem R_props : ∀ c ∈ U.R, c.EffTyped U.L.lets ∧ c.Guarded := by
  obtain ⟨hRC, -, -, hcases⟩ := realization_structure U.hR
  obtain ⟨hnl, hspec⟩ := typeLets_spec U.lets_body U.wf.nodup U.hT
  have hΓfin : ∀ e, (U.T.Γ e).isSome → IsLet U.L.lets e := by
    intro e he; by_contra hc; rw [(hnl e hc).1] at he; simp at he
  intro c hc
  rcases hcases c hc with hc | ⟨p, f, hf, hcf⟩ | ⟨p, g, hg, hcg⟩
  · -- a clause of the rewriting of the main formula
    refine ⟨U.typed_hyps U.T.Γ hΓfin U.hrw ?_ U.C U.hC c hc, fun κ hκ => ?_⟩
    · rw [Formula.WellArity, atoms_bigAnd]
      rintro a ⟨χ, hχ, ha⟩; exact U.wf.arity.2 χ hχ a ha
    · have h := guard_rw U.hrw U.C U.hC c hc κ hκ
      have hfv : (bigAnd U.L.chis).fv = ∅ := by
        rw [fv_bigAnd]; ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨χ, hχ, hx⟩; rw [U.wf.closed χ hχ] at hx; exact hx
      rwa [hfv, Set.union_empty] at h
  · by_cases hp : IsLet U.L.lets p
    · obtain ⟨d, hd, rfl⟩ := hp
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
      obtain ⟨Tk, -, hTk, -, hCC, -⟩ := hspec k hk
      obtain ⟨body, 𝒞, C₀, hr, hC₀, rfl, hfvb, -, hat, -⟩ := hCC f hf
      obtain ⟨c₀, hc₀, rfl⟩ := hcf
      have hΓk : ∀ e, (Tk.Γ e).isSome → IsLet U.L.lets e := by
        intro e he; obtain ⟨k', -, hk', rfl⟩ := hTk e he; exact ⟨_, List.getElem_mem hk', rfl⟩
      refine ⟨U.typed_hyps Tk.Γ hΓk hr (WellArity.mono (U.wf.arity.1 _ hd) hat) C₀ hC₀ c₀ hc₀,
        fun κ' hκ' => ?_⟩
      simp only [List.mem_map] at hκ'
      obtain ⟨κ, hκ, rfl⟩ := hκ'
      have h := guard_rw hr C₀ hC₀ c₀ hc₀ κ hκ
      intro y hy
      rcases h hy with hy | hy
      · rw [fv_gconj] at hy ⊢
        obtain ⟨γ, hγ, hy⟩ := hy
        exact ⟨γ, List.mem_append_left _ hγ, hy⟩
      · have hy' : y ∈ U.L.lets[k].xs := by
          have := hfvb hy; rw [U.wf.fv_let _ hd] at this; exact this
        rw [fv_gconj]
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        simp only [GAtom.toFormula, Formula.fv, varsList_map_var']
        exact hy'
    · rw [(hnl p hp).2.1] at hf; exact absurd hf (Set.notMem_empty _)
  · by_cases hp : IsLet U.L.lets p
    · obtain ⟨d, hd, rfl⟩ := hp
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
      obtain ⟨Tk, -, hTk, -, -, hCS⟩ := hspec k hk
      obtain ⟨bs, hbs, rfl, -⟩ := hCS g hg
      obtain ⟨c₀, ⟨b, hb, hc₀⟩, rfl⟩ := hcg
      obtain ⟨hr, hC, hfvb, -, hat⟩ := hbs b hb
      have hΓk : ∀ e, (Tk.Γ e).isSome → IsLet U.L.lets e := by
        intro e he; obtain ⟨k', -, hk', rfl⟩ := hTk e he; exact ⟨_, List.getElem_mem hk', rfl⟩
      refine ⟨U.typed_hyps Tk.Γ hΓk hr (WellArity.mono (U.wf.arity.1 _ hd) hat) b.2.2 hC c₀ hc₀,
        fun κ' hκ' => ?_⟩
      simp only [List.mem_map] at hκ'
      obtain ⟨κ, hκ, rfl⟩ := hκ'
      have h := guard_rw hr b.2.2 hC c₀ hc₀ κ hκ
      intro y hy
      rcases h hy with hy | hy
      · rw [fv_gconj] at hy ⊢
        obtain ⟨γ, hγ, hy⟩ := hy
        exact ⟨γ, List.mem_append_left _ hγ, hy⟩
      · have hy' : y ∈ U.L.lets[k].xs := by
          have := hfvb hy; rw [U.wf.fv_let _ hd] at this; exact this
        rw [fv_gconj]
        refine ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
        simp only [GAtom.toFormula, Formula.fv, varsList_map_var']
        exact hy'
    · rw [(hnl p hp).2.2] at hg; exact absurd hg (Set.notMem_empty _)

end Setup

end Paper
