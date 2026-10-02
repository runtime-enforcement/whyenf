/-
  Rank locality: a trigger only depends on events of lower or equal rank.
-/
import Paper.Proof.RProps

namespace Paper

open Classical

variable {Voc : Vocabulary}

namespace Setup
variable (U : Setup Voc)

/-- The names whose let-support lies in `N`. -/
def Supp (N : Set Voc.ℰ) : Set Voc.ℰ := {q | ∀ e, Decomp U.L.lets q e → e ∈ N}

theorem supp_base {N : Set Voc.ℰ} {q : Voc.ℰ} (hq : ¬ IsLet U.L.lets q) : q ∈ U.Supp N ↔ q ∈ N := by
  constructor
  · intro h; exact h q (.base hq)
  · intro h e he
    cases he with
    | base => exact h
    | let_ hd _ _ => exact absurd ⟨_, hd, rfl⟩ hq

/-- **`applyLets` respects agreement on supports.** -/
theorem applyLets_agree {S₀ S₀' : Str Voc.toSignature} {N : Set Voc.ℰ} (h : S₀.Agree S₀' N)
    (h₀ : ∀ j, ∀ ev ∈ S₀.D j, ¬ IsLet U.L.lets ev.e)
    (h₀' : ∀ j, ∀ ev ∈ S₀'.D j, ¬ IsLet U.L.lets ev.e) :
    (applyLets U.L.lets S₀).Agree (applyLets U.L.lets S₀') (U.Supp N) := by
  set ℒ := U.L.lets
  have hA := applyLets_spec' ℒ U.wf.nodup U.scope_names S₀ h₀ ℒ.length le_rfl
  have hA' := applyLets_spec' ℒ U.wf.nodup U.scope_names S₀' h₀' ℒ.length le_rfl
  rw [List.take_length] at hA hA'
  obtain ⟨-, hb, hd⟩ := hA
  obtain ⟨-, hb', hd'⟩ := hA'
  refine ⟨by rw [applyLets_τ, applyLets_τ, h.1], ?_⟩
  -- by strong induction on the let index
  have key : ∀ k (hk : k < ℒ.length), ℒ[k].e ∈ U.Supp N → ∀ j ev, ev.e = ℒ[k].e →
      (ev ∈ (applyLets ℒ S₀).D j ↔ ev ∈ (applyLets ℒ S₀').D j) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk hs j ev he
      rw [(hd k hk hk j ev he), (hd' k hk hk j ev he)]
      refine exists_congr fun v' => and_congr_right fun _ => and_congr_right fun _ => ?_
      refine Formula.sat_agree _ _ _ _ _ ⟨by rw [applyLets_τ, applyLets_τ, h.1], fun j' ev' hev' => ?_⟩
      -- the names of the body
      rcases U.scope_names k hk ev'.e hev' with hq | ⟨k', hk', hk'l, he'⟩
      · rw [hb j' ev' fun m hm _ h' => hq ⟨_, List.getElem_mem hm, h'.symm⟩,
          hb' j' ev' fun m hm _ h' => hq ⟨_, List.getElem_mem hm, h'.symm⟩]
        have hpred : ev'.e ∈ ℒ[k].φ.preds := by
          rwa [← Formula.names_eq_preds (IsLetBody.noLet (U.lets_body _ (List.getElem_mem hk)))]
        exact h.2 j' ev' (hs ev'.e (.let_ (List.getElem_mem hk) hpred (.base hq)))
      · refine ih k' hk' hk'l (fun e he₂ => hs e ?_) j' ev' he'.symm
        have hpred : ℒ[k'].e ∈ ℒ[k].φ.preds := by
          rw [he', ← Formula.names_eq_preds (IsLetBody.noLet (U.lets_body _ (List.getElem_mem hk)))]
          exact hev'
        exact .let_ (List.getElem_mem hk) hpred he₂
  intro j ev hev
  by_cases hq : IsLet ℒ ev.e
  · obtain ⟨d, hdm, hde⟩ := hq
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hdm
    exact key k hk (hde ▸ hev) j ev hde.symm
  · rw [hb j ev fun m hm _ h' => hq ⟨_, List.getElem_mem hm, h'.symm⟩,
      hb' j ev fun m hm _ h' => hq ⟨_, List.getElem_mem hm, h'.symm⟩]
    exact h.2 j ev ((U.supp_base hq).1 hev)

/-- The EDG bounds the ranks of the supports of a trigger. -/
theorem trig_rank {c : EClause Voc} (hc : c ∈ U.R) {q : Voc.ℰ} (hq : q ∈ c.trigPreds) {e : Voc.ℰ}
    (he : Decomp U.L.lets q e) : U.rk e ≤ U.rk c.ε.name :=
  U.topo.2 e c.ε.name ⟨c, c.ε.pol, hc, ⟨q, hq, he⟩, rfl, (U.R_props c hc).1.2, rfl⟩

end Setup

end Paper
