/-
  What Algorithm 3 (`TypeLet`, `TypeLets`) computes.
-/
import Paper.Proof.RwSound

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-- `gate` on one clause set. -/
def gateSet (q : Voc.ℰ) (xs : List Voc.𝕍) (C : Set (EClause Voc)) : Set (EClause Voc) :=
  (fun c => ⟨c.π.map (· ++ [.pred q (xs.map Term.var)]), c.ψ, c.ε⟩) '' C

theorem mem_gate {q : Voc.ℰ} {xs : List Voc.𝕍} {𝒞 : CSet Voc} {f : Set (EClause Voc)} :
    f ∈ gate q xs 𝒞 ↔ ∃ C ∈ 𝒞, f = gateSet q xs C := Iff.rfl

/-- `stripExists` of a let body of a valid LNF is the body itself, unless the
    body is present (`IsPsi`). -/
theorem stripExists_exs (ys : List Voc.𝕍) (χ : Formula Voc) :
    stripExists (Formula.exs ys χ) = stripExists χ := by
  induction ys with
  | nil => rfl
  | cons y ys ih => simp [Formula.exs, stripExists] at ih ⊢; exact ih

theorem IsChi_stripExists : ∀ {χ : Formula Voc}, χ.IsChi →
    (∀ I φl φr, stripExists χ ≠ .since I φl φr) ∧ (∀ I φ, stripExists χ ≠ .prev I φ) ∧
      (∀ ys ω ss gs φ, stripExists χ ≠ .agg ys ω ss gs φ)
  | .ex x φ, h => by simp only [stripExists]; exact IsChi_stripExists h.2
  | .top, _ | .pred .., _ | .eq .., _ | .neg _, _ | .and .., _ | .next .., _ | .eventually .., _ =>
    by simp [stripExists]
  | .prev .., h | .since .., h | .letin .., h | .agg .., h => by simp [Formula.IsChi] at h

theorem letBody_since {ψ φl φr : Formula Voc} {I : Interval} (hb : ψ.IsLetBody)
    (h : stripExists ψ = .since I φl φr) : ψ = .since I φl φr := by
  rcases hb with ⟨ys, χ, rfl, hχ⟩ | ⟨I', ψ', rfl, -⟩ | ⟨I', l, r, rfl, -⟩ | ⟨ys, ω, ss, gs, ψ', rfl, -⟩
  · rw [stripExists_exs] at h; exact absurd h ((IsChi_stripExists hχ).1 _ _ _)
  · simp [stripExists] at h
  · simpa [stripExists] using h
  · simp [stripExists] at h

/-! ## One `TypeLet` -/

section
variable {Ξ : RwSetting Voc} {T T' : Typed Voc} {p : Voc.ℰ} {xs : List Voc.𝕍} {ψ : Formula Voc}

theorem typeLet_frame (h : TypeLet Ξ T p xs ψ = some T') :
    (∀ e, e ≠ p → T'.Γ e = T.Γ e ∧ T'.CC e = T.CC e ∧ T'.CS e = T.CS e) ∧ (T'.Γ p).isSome := by
  unfold TypeLet at h
  generalize stripExists ψ = χ at h
  cases χ with
  | since I φl φr =>
    cases φl <;> simp only at h <;> split_ifs at h <;> cases h <;>
      exact ⟨fun e he => by simp [Function.update_of_ne he], by simp⟩
  | prev | agg =>
    simp only at h; split_ifs at h; cases h
    exact ⟨fun e he => by simp [Function.update_of_ne he], by simp⟩
  | _ =>
    simp only at h; split_ifs at h <;> cases h <;>
      exact ⟨fun e he => by simp [Function.update_of_ne he], by simp⟩

/-- The causation clauses of `p` realize a formula that implies `p`'s body. -/
def CauSpec (Ξ : RwSetting Voc) (Γ : LetCtx Voc) (p : Voc.ℰ) (xs : List Voc.𝕍) (ψ : Formula Voc)
    (f : Set (EClause Voc)) : Prop :=
  ∃ body 𝒞 C, Rw Ξ Γ .C body 𝒞 ∧ C ∈ 𝒞 ∧ f = gateSet (Ξ.cauN p) xs C ∧
    body.fv ⊆ ψ.fv ∧ (∀ G, ψ.Clean G → body.Clean G) ∧ body.atoms ⊆ ψ.atoms ∧
    ∀ S v i, body.sat S v i → ψ.sat S v i

/-- The suppression clauses of `p` realize formulas whose negations imply that
    of `p`'s body. -/
def SupSpec (Ξ : RwSetting Voc) (Γ : LetCtx Voc) (p : Voc.ℰ) (xs : List Voc.𝕍) (ψ : Formula Voc)
    (f : Set (EClause Voc)) : Prop :=
  ∃ bs : List (Formula Voc × CSet Voc × Set (EClause Voc)),
    (∀ b ∈ bs, Rw Ξ Γ .S b.1 b.2.1 ∧ b.2.2 ∈ b.2.1 ∧ b.1.fv ⊆ ψ.fv ∧
      (∀ G, ψ.Clean G → b.1.Clean G) ∧ b.1.atoms ⊆ ψ.atoms) ∧
    f = gateSet (Ξ.supN p) xs {c | ∃ b ∈ bs, c ∈ b.2.2} ∧
    ∀ S v i, (∀ b ∈ bs, ¬ b.1.sat S v i) → ¬ ψ.sat S v i

theorem typeLet_CC (hb : ψ.IsLetBody) (h : TypeLet Ξ T p xs ψ = some T') (h0 : T.CC p = ∅)
    {f : Set (EClause Voc)} (hf : f ∈ T'.CC p) : CauSpec Ξ T.Γ p xs ψ f := by
  unfold TypeLet at h
  generalize hχ : stripExists ψ = χ at h
  cases χ with
  | since I φl φr =>
    have hψ := letBody_since hb hχ; subst hψ
    have hsince : ∀ S v i, φr.sat S v i → 0 ∈ I → (Formula.since I φl φr).sat S v i :=
      fun S v i h hI => ⟨i, le_rfl, by simpa using hI, h, fun k h1 h2 => absurd h2 (by omega)⟩
    have hcl : ∀ G, (Formula.since I φl φr).Clean G → φr.Clean G :=
      fun G h => h.2.mono Set.subset_union_left
    simp only at h
    split at h
    all_goals (try (have heq := ‹Formula.since _ _ _ = _›; cases heq))
    · split_ifs at h with h1 h2 <;> cases h <;>
        simp only [Function.update_self, Set.mem_empty_iff_false] at hf
      obtain ⟨C, ⟨𝒞, hr, hC⟩, rfl⟩ := hf
      exact ⟨_, 𝒞, C, hr, hC, rfl, Set.subset_union_right, hcl, Set.subset_union_right,
        fun S v i hs => hsince S v i hs h2⟩
    · split_ifs at h with h1 h2 <;> cases h <;>
        simp only [Function.update_self, Set.mem_empty_iff_false] at hf
      obtain ⟨C, ⟨𝒞, hr, hC⟩, rfl⟩ := hf
      exact ⟨_, 𝒞, C, hr, hC, rfl, Set.subset_union_right, hcl, Set.subset_union_right,
        fun S v i hs => hsince S v i hs h2⟩
    · exfalso; rename_i h4; exact h4 _ _ _ rfl
  | prev | agg =>
    simp only at h; split_ifs at h; cases h
    simp at hf
  | _ =>
    simp only at h; split_ifs at h <;> cases h
    · rw [h0] at hf; exact absurd hf (Set.notMem_empty _)
    · simp only [Function.update_self] at hf
      obtain ⟨C, ⟨𝒞, hr, hC⟩, rfl⟩ := hf
      exact ⟨ψ, 𝒞, C, hr, hC, rfl, le_rfl, fun _ h => h, le_rfl, fun _ _ _ h => h⟩
    · simp at hf

theorem typeLet_CS (hb : ψ.IsLetBody) (h : TypeLet Ξ T p xs ψ = some T') (h0 : T.CS p = ∅)
    {f : Set (EClause Voc)} (hf : f ∈ T'.CS p) : SupSpec Ξ T.Γ p xs ψ f := by
  unfold TypeLet at h
  generalize hχ : stripExists ψ = χ at h
  cases χ with
  | since I φl φr =>
    have hψ := letBody_since hb hχ; subst hψ
    have hl : ∀ G, (Formula.since I φl φr).Clean G → φl.Clean G :=
      fun G h => h.1.mono Set.subset_union_left
    have hr' : ∀ G, (Formula.since I φl φr).Clean G → φr.Clean G :=
      fun G h => h.2.mono Set.subset_union_left
    simp only at h
    split at h
    all_goals (try (have heq := ‹Formula.since _ _ _ = _›; cases heq))
    · split_ifs at h <;> cases h <;> simp at hf
    rotate_left
    · exfalso; rename_i h4; exact h4 _ _ _ rfl
    · split_ifs at h with h1 h2 <;> cases h <;>
        simp only [Function.update_self] at hf
      · obtain ⟨C, ⟨C₁, ⟨𝒞₁, r₁, m₁⟩, C₂, ⟨𝒞₂, r₂, m₂⟩, rfl⟩, rfl⟩ := hf
        refine ⟨[(φl, 𝒞₁, C₁), (φr, 𝒞₂, C₂)], ?_, ?_, ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro b (rfl | rfl)
          · exact ⟨r₁, m₁, Set.subset_union_left, hl, Set.subset_union_left⟩
          · exact ⟨r₂, m₂, Set.subset_union_right, hr', Set.subset_union_right⟩
        · congr 1; ext c; simp
        · rintro S v i hn ⟨j, hj, -, hr, hlk⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hn
          rcases Nat.lt_or_ge j i with hji | hji
          · exact hn.1 (hlk i hji le_rfl)
          · exact hn.2 (by rwa [show j = i by omega] at hr)
      · obtain ⟨C, ⟨𝒞₁, r₁, m₁⟩, rfl⟩ := hf
        refine ⟨[(φl, 𝒞₁, C)], ?_, ?_, ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro b rfl
          exact ⟨r₁, m₁, Set.subset_union_left, hl, Set.subset_union_left⟩
        · congr 1; ext c; simp
        · rintro S v i hn ⟨j, hj, hI, -, hlk⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hn
          rcases Nat.lt_or_ge j i with hji | hji
          · exact hn (hlk i hji le_rfl)
          · rw [show j = i by omega, Nat.sub_self] at hI; exact h2 hI
  | prev | agg =>
    simp only at h; split_ifs at h; cases h
    simp at hf
  | _ =>
    simp only at h; split_ifs at h <;> cases h
    · rw [h0] at hf; exact absurd hf (Set.notMem_empty _)
    · simp only [Function.update_self] at hf
      obtain ⟨C, ⟨𝒞, hr, hC⟩, rfl⟩ := hf
      refine ⟨[(ψ, 𝒞, C)], ?_, ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro b rfl; exact ⟨hr, hC, le_rfl, fun _ h => h, le_rfl⟩
      · congr 1; ext c; simp
      · intro S v i hn; exact hn (ψ, 𝒞, C) (by simp)
    · simp at hf

end

/-! ## The fold `TypeLets` -/

section
variable {Ξ : RwSetting Voc} {ℒ : List (LetDef Voc)}

theorem TypeLets_take_succ (k : ℕ) (hk : k < ℒ.length) :
    TypeLets Ξ (ℒ.take (k + 1)) =
      (TypeLets Ξ (ℒ.take k)).bind fun T => TypeLet Ξ T ℒ[k].e ℒ[k].xs ℒ[k].φ := by
  simp only [TypeLets]
  rw [List.take_succ_eq_append_getElem hk, List.foldlM_append]
  simp [Option.bind_eq_bind]

theorem TypeLets_take_isSome {T : Typed Voc} (h : TypeLets Ξ ℒ = some T) :
    ∀ k ≤ ℒ.length, ∃ Tk, TypeLets Ξ (ℒ.take k) = some Tk := by
  intro k hk
  have : TypeLets Ξ ℒ = (TypeLets Ξ (ℒ.take k)).bind fun T =>
      (ℒ.drop k).foldlM (fun T d => TypeLet Ξ T d.e d.xs d.φ) T := by
    conv_lhs => rw [← List.take_append_drop k ℒ]
    simp only [TypeLets]; rw [List.foldlM_append]; simp [Option.bind_eq_bind]
  rw [h] at this
  cases hT : TypeLets Ξ (ℒ.take k) with
  | none => rw [hT] at this; simp at this
  | some Tk => exact ⟨Tk, rfl⟩

theorem TypeLets_take_len {T : Typed Voc} (h : TypeLets Ξ ℒ = some T) :
    TypeLets Ξ (ℒ.take ℒ.length) = some T := by simpa using h

/-- Names not yet typed are untouched. -/
theorem TypeLets_take_fresh :
    ∀ k (_ : k ≤ ℒ.length), ∀ Tk, TypeLets Ξ (ℒ.take k) = some Tk →
      ∀ e, (∀ k' (hk' : k' < k), (ℒ[k']'(by omega)).e ≠ e) →
        Tk.Γ e = none ∧ Tk.CC e = ∅ ∧ Tk.CS e = ∅
  | 0, _, Tk, h, e, _ => by simp [TypeLets] at h; subst h; simp
  | k + 1, hk, Tk, h, e, he => by
    rw [TypeLets_take_succ k (by omega)] at h
    obtain ⟨Tk', h1, h2⟩ := Option.bind_eq_some_iff.1 h
    have ih := TypeLets_take_fresh k (by omega) Tk' h1 e fun k' hk' => he k' (by omega)
    obtain ⟨hf, -⟩ := typeLet_frame h2
    obtain ⟨a, b, c⟩ := hf e (Ne.symm (he k (by omega)))
    exact ⟨a.trans ih.1, b.trans ih.2.1, c.trans ih.2.2⟩

theorem names_inj (hnd : (ℒ.map LetDef.e).Nodup) {i j : ℕ} (hi : i < ℒ.length) (hj : j < ℒ.length)
    (h : ℒ[i].e = ℒ[j].e) : i = j := by
  have h1 := List.inj_on_of_nodup_map hnd (List.getElem_mem hi) (List.getElem_mem hj) h
  exact (List.Nodup.getElem_inj_iff (List.Nodup.of_map _ hnd)).1 h1

/-- After the `k`-th let, later lets do not change its entries. -/
theorem TypeLets_take_stable (hnd : (ℒ.map LetDef.e).Nodup) (k : ℕ) (hk : k < ℒ.length) :
    ∀ n, k < n → n ≤ ℒ.length → ∀ Tk Tn, TypeLets Ξ (ℒ.take (k + 1)) = some Tk →
      TypeLets Ξ (ℒ.take n) = some Tn →
      Tn.Γ ℒ[k].e = Tk.Γ ℒ[k].e ∧ Tn.CC ℒ[k].e = Tk.CC ℒ[k].e ∧ Tn.CS ℒ[k].e = Tk.CS ℒ[k].e
  | 0, h, _, _, _, _, _ => absurd h (by omega)
  | n + 1, h, hn, Tk, Tn, hTk, hTn => by
    rcases Nat.lt_or_ge k n with hkn | hkn
    · rw [TypeLets_take_succ n (by omega)] at hTn
      obtain ⟨Tn', h1, h2⟩ := Option.bind_eq_some_iff.1 hTn
      have ih := TypeLets_take_stable hnd k hk n hkn (by omega) Tk Tn' hTk h1
      obtain ⟨hf, -⟩ := typeLet_frame h2
      have hne : ℒ[k].e ≠ ℒ[n].e := by
        intro heq; have := names_inj hnd hk (by omega) heq; omega
      obtain ⟨a, b, c⟩ := hf _ hne
      exact ⟨a.trans ih.1, b.trans ih.2.1, c.trans ih.2.2⟩
    · have : n = k := by omega
      subst this
      rw [hTk] at hTn; cases hTn; exact ⟨rfl, rfl, rfl⟩

/-- **What Algorithm 3 computes.** -/
theorem typeLets_spec (hb : ∀ d ∈ ℒ, d.φ.IsLetBody) (hnd : (ℒ.map LetDef.e).Nodup)
    {T : Typed Voc} (h : TypeLets Ξ ℒ = some T) :
    (∀ e, ¬ IsLet ℒ e → T.Γ e = none ∧ T.CC e = ∅ ∧ T.CS e = ∅) ∧
    ∀ k (hk : k < ℒ.length), ∃ Tk, TypeLets Ξ (ℒ.take k) = some Tk ∧
      (∀ e, (Tk.Γ e).isSome → ∃ k' < k, ∃ hk' : k' < ℒ.length, ℒ[k'].e = e) ∧
      (T.Γ ℒ[k].e).isSome ∧
      (∀ f ∈ T.CC ℒ[k].e, CauSpec Ξ Tk.Γ ℒ[k].e ℒ[k].xs ℒ[k].φ f) ∧
      (∀ f ∈ T.CS ℒ[k].e, SupSpec Ξ Tk.Γ ℒ[k].e ℒ[k].xs ℒ[k].φ f) := by
  have hlen := TypeLets_take_len h
  refine ⟨fun e he => TypeLets_take_fresh ℒ.length le_rfl T hlen e fun k' hk' h' =>
    he ⟨_, List.getElem_mem hk', h'⟩, fun k hk => ?_⟩
  obtain ⟨Tk, hTk⟩ := TypeLets_take_isSome h k hk.le
  obtain ⟨Tk1, hTk1⟩ := TypeLets_take_isSome h (k + 1) hk
  have hstep := hTk1
  rw [TypeLets_take_succ k hk, hTk] at hstep
  simp only [Option.bind_some] at hstep
  have hst := TypeLets_take_stable hnd k hk ℒ.length hk le_rfl Tk1 T hTk1 hlen
  have hfr := TypeLets_take_fresh k hk.le Tk hTk ℒ[k].e fun k' hk' heq => by
    have := names_inj hnd (by omega) hk heq; omega
  refine ⟨Tk, hTk, fun e he => ?_, ?_, fun f hf => ?_, fun f hf => ?_⟩
  · by_contra hc; push Not at hc
    have := (TypeLets_take_fresh k hk.le Tk hTk e fun k' hk' h' => hc k' hk' (by omega) h').1
    rw [this] at he; simp at he
  · rw [hst.1]; exact (typeLet_frame hstep).2
  · rw [hst.2.1] at hf
    exact typeLet_CC (hb _ (List.getElem_mem hk)) hstep hfr.2.1 hf
  · rw [hst.2.2] at hf
    exact typeLet_CS (hb _ (List.getElem_mem hk)) hstep hfr.2.2 hf

end

end Paper
