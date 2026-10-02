/-
  The structure `applyLets ℒ S₀` (the semantics of the lets of an LNF).
-/
import Paper.Proof.Guarded

namespace Paper

variable {Voc : Vocabulary}

/-- The `d.e`-events of `S` are those defined by `d`. -/
def LetDef.Defined (S : Str Voc.toSignature) (d : LetDef Voc) : Prop :=
  ∀ j (ev : Event Voc.toSignature), ev.e = d.e →
    (ev ∈ S.D j ↔ ∃ v' : Val Voc, v'.Covers d.φ.fv ∧ d.xs.map v' = ev.args.map some ∧ d.φ.sat S v' j)

/-- No `let` inside. -/
def Formula.NoLet : Formula Voc → Prop
  | .letin .. => False
  | .neg φ | .ex _ φ | .next _ φ | .prev _ φ | .eventually _ φ | .agg _ _ _ _ φ => φ.NoLet
  | .and φ ψ | .since _ φ ψ => φ.NoLet ∧ ψ.NoLet
  | _ => True

theorem Formula.names_eq_preds : ∀ {φ : Formula Voc}, φ.NoLet → φ.names = φ.preds
  | .top, _ => by simp [Formula.names, Formula.preds, Formula.atoms]
  | .pred e ts, _ => by simp [Formula.names, Formula.preds, Formula.atoms]
  | .eq _ _, _ => by simp [Formula.names, Formula.preds, Formula.atoms]
  | .neg φ, h | .ex _ φ, h | .next _ φ, h | .prev _ φ, h | .eventually _ φ, h | .agg _ _ _ _ φ, h => by
    simp only [Formula.names, Formula.preds, Formula.atoms] at h ⊢
    exact Formula.names_eq_preds h
  | .and φ ψ, h | .since _ φ ψ, h => by
    simp only [Formula.names, Formula.preds, Formula.atoms, Set.image_union] at h ⊢
    rw [Formula.names_eq_preds h.1, Formula.names_eq_preds h.2]; rfl
  | .letin .., h => h.elim

theorem IsChi.noLet : ∀ {χ : Formula Voc}, χ.IsChi → χ.NoLet
  | .top, _ | .pred .., _ | .eq .., _ => trivial
  | .neg φ, h => IsChi.noLet (χ := φ) h
  | .and φ ψ, h => ⟨IsChi.noLet h.1, IsChi.noLet h.2⟩
  | .ex _ φ, h => show φ.NoLet from IsChi.noLet h.2
  | .next _ φ, h => IsChi.noLet (χ := φ) h
  | .eventually _ φ, h => IsChi.noLet (χ := φ) h
  | .prev .., h | .since .., h | .letin .., h | .agg .., h => by simp [Formula.IsChi] at h

theorem exs_noLet (ys : List Voc.𝕍) {χ : Formula Voc} (h : χ.NoLet) : (Formula.exs ys χ).NoLet := by
  induction ys with
  | nil => exact h
  | cons y ys ih => exact ih

theorem IsPsi.noLet {ψ : Formula Voc} (h : ψ.IsPsi) : ψ.NoLet := by
  obtain ⟨ys, χ, rfl, hχ⟩ := h; exact exs_noLet ys (IsChi.noLet hχ)

theorem IsLetBody.noLet {φ : Formula Voc} (h : φ.IsLetBody) : φ.NoLet := by
  rcases h with h | ⟨I, ψ, rfl, h⟩ | ⟨I, l, r, rfl, hl, hr⟩ | ⟨ys, ω, ss, gs, ψ, rfl, h⟩
  · exact IsPsi.noLet h
  · exact show ψ.NoLet from IsPsi.noLet h
  · exact ⟨IsPsi.noLet hl, IsPsi.noLet hr⟩
  · exact show ψ.NoLet from IsPsi.noLet h

section
variable (ℒ : List (LetDef Voc))

/-- The structure of `applyLets ℒ S₀`. -/
theorem applyLets_spec' (hnd : (ℒ.map LetDef.e).Nodup)
    (hscope : ∀ k (hk : k < ℒ.length), ∀ e ∈ ℒ[k].φ.names,
      ¬ IsLet ℒ e ∨ ∃ k' < k, ∃ hk' : k' < ℒ.length, ℒ[k'].e = e)
    (S₀ : Str Voc.toSignature) (h₀ : ∀ j, ∀ ev ∈ S₀.D j, ¬ IsLet ℒ ev.e) :
    ∀ n ≤ ℒ.length, (applyLets (ℒ.take n) S₀).τ = S₀.τ ∧
      (∀ j ev, (∀ k (hk : k < ℒ.length), k < n → ev.e ≠ ℒ[k].e) →
        (ev ∈ (applyLets (ℒ.take n) S₀).D j ↔ ev ∈ S₀.D j)) ∧
      ∀ k (hk : k < ℒ.length), k < n → LetDef.Defined (applyLets (ℒ.take n) S₀) ℒ[k] := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, fun _ _ _ => Iff.rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn
    obtain ⟨iτ, iD, iDef⟩ := ih (by omega)
    have hnl : n < ℒ.length := by omega
    set d := ℒ[n] with hd
    set Sn := applyLets (ℒ.take n) S₀
    have hstep : applyLets (ℒ.take (n + 1)) S₀ =
        Sn.extend d.e d.xs d.φ.fv (fun v' j => d.φ.sat Sn v' j) := by
      simp only [applyLets, Sn, List.take_add_one, List.getElem?_eq_getElem hnl, Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil, d]
    rw [hstep]
    have hnot : ∀ m (hm : m < ℒ.length), m < n → ℒ[m].e ≠ d.e := fun m hm hmn h =>
      absurd (names_inj hnd hm hnl h) (by omega)
    have hagree : ∀ N : Set Voc.ℰ, d.e ∉ N →
        Sn.Agree (Sn.extend d.e d.xs d.φ.fv (fun v' j => d.φ.sat Sn v' j)) N := by
      intro N hN
      refine ⟨rfl, fun j ev hev => ?_⟩
      simp only [Str.extend, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · exact Or.inl
      · rintro (h | ⟨he, _⟩)
        · exact h
        · exact absurd (he ▸ hev) hN
    have hnotin : ∀ k (hk : k < ℒ.length), k ≤ n → d.e ∉ ℒ[k].φ.names := by
      intro k hk hkn hmem
      rcases hscope k hk d.e hmem with h | ⟨k', hk', hk'l, he⟩
      · exact h ⟨d, List.getElem_mem hnl, rfl⟩
      · exact hnot k' hk'l (by omega) he
    refine ⟨iτ, ?_, ?_⟩
    · intro j ev hev
      simp only [Str.extend, Set.mem_union, Set.mem_setOf_eq]
      rw [← iD j ev (fun k hk hkn => hev k hk (by omega))]
      constructor
      · rintro (h | ⟨he, _⟩)
        · exact h
        · exact absurd he (hev n hnl (by omega))
      · exact Or.inl
    · intro k hk hkn
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hkn) with hlt | heq
      · intro j ev he
        have hne : ev.e ≠ d.e := he ▸ hnot k hk hlt
        rw [← ((hagree {x | x ≠ d.e} (by simp)).2 j ev hne), iDef k hk hlt j ev he]
        refine exists_congr fun v' => and_congr_right fun _ => and_congr_right fun _ => ?_
        exact Formula.sat_agree _ _ _ _ _ (hagree _ (hnotin k hk hlt.le))
      · subst heq
        intro j ev he
        simp only [Str.extend, Set.mem_union, Set.mem_setOf_eq]
        have h0 : ev ∉ Sn.D j := by
          intro hev
          rw [iD j ev (fun m hm hmn => he ▸ hnot m hm hmn |>.symm)] at hev
          exact h₀ j ev hev ⟨d, List.getElem_mem hnl, he.symm⟩
        constructor
        · rintro (h | ⟨-, v', hv', hxs, hs⟩)
          · exact absurd h h0
          · exact ⟨v', hv', hxs, (Formula.sat_agree _ _ _ _ _ (hagree _ (hnotin _ hnl le_rfl))).1 hs⟩
        · rintro ⟨v', hv', hxs, hs⟩
          exact Or.inr ⟨he, v', hv', hxs,
            (Formula.sat_agree _ _ _ _ _ (hagree _ (hnotin _ hnl le_rfl))).2 hs⟩

end

end Paper
