/-
  Theorem 4.3 instantiated with the let-normal form of Theorem 4.1
  (NOTES.md, "Theorem 4.3 with the let-normal form of Theorem 4.1").
-/
import Paper.Proof.Main

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-! ## Embedding into an extended vocabulary -/

section ext
variable {L : Type} [Finite L] {ιL : L → ℕ}

theorem Formula.fv_embed : ∀ φ : Formula Voc, (φ.embed (L := L) (ιL := ιL)).fv = φ.fv
  | .top => rfl
  | .pred _ ts => Term.varsList_embed ts
  | .neg φ => Formula.fv_embed φ
  | .and φ ψ => by simp only [Formula.embed, Formula.fv, Formula.fv_embed φ, Formula.fv_embed ψ]; rfl
  | .ex x φ => by simp only [Formula.embed, Formula.fv, Formula.fv_embed φ]; rfl
  | .next _ φ => Formula.fv_embed φ
  | .prev _ φ => Formula.fv_embed φ
  | .eventually _ φ => Formula.fv_embed φ
  | .since _ φ ψ => by simp only [Formula.embed, Formula.fv, Formula.fv_embed φ, Formula.fv_embed ψ]; rfl
  | .letin _ _ _ ψ => Formula.fv_embed ψ
  | .agg .. => rfl
  | .eq .. => rfl

theorem Formula.isMFOTL_embed : ∀ {φ : Formula Voc}, φ.IsMFOTL →
    (φ.embed (L := L) (ιL := ιL)).IsMFOTL
  | .top, _ | .pred .., _ | .eq .., _ => trivial
  | .neg φ, h | .ex _ φ, h | .next _ φ, h | .prev _ φ, h | .eventually _ φ, h | .agg _ _ _ _ φ, h =>
    Formula.isMFOTL_embed (φ := φ) h
  | .and φ ψ, h | .since _ φ ψ, h | .letin _ _ φ ψ, h =>
    ⟨Formula.isMFOTL_embed (φ := φ) h.1, Formula.isMFOTL_embed (φ := ψ) h.2⟩

theorem Formula.atoms_embed : ∀ φ : Formula Voc, ∀ a ∈ (φ.embed (L := L) (ιL := ιL)).atoms,
    a.1 ∈ Set.range Sum.inl
  | .top, _, h | .eq .., _, h => absurd h (Set.notMem_empty _)
  | .pred e ts, a, h => by simp only [Formula.embed, Formula.atoms, Set.mem_singleton_iff] at h; subst h; exact ⟨e, rfl⟩
  | .neg φ, a, h | .ex _ φ, a, h | .next _ φ, a, h | .prev _ φ, a, h | .eventually _ φ, a, h
  | .agg _ _ _ _ φ, a, h => Formula.atoms_embed φ a h
  | .and φ ψ, a, h | .since _ φ ψ, a, h | .letin _ _ φ ψ, a, h => by
    rcases h with h | h
    · exact Formula.atoms_embed φ a h
    · exact Formula.atoms_embed ψ a h

/-- The events of `S` with an original name, as a structure over `Voc`. -/
def Str.restrict (S : Str (Voc.ext L ιL).toSignature) : Str Voc.toSignature where
  τ := S.τ
  D := fun j => {ev | (⟨Sum.inl ev.e, ev.args, ev.arity⟩ : Event (Voc.ext L ιL).toSignature) ∈ S.D j}

theorem Str.restrict_extend (S : Str (Voc.ext L ιL).toSignature) (e : Voc.ℰ) (xs : List Voc.𝕍)
    (F : Set Voc.𝕍) (P : Val Voc → ℕ → Prop) :
    (S.extend (Sum.inl e) xs F P).restrict = (S.restrict).extend e xs F P := by
  simp only [Str.restrict, Str.extend]
  congr 1
  funext j; ext ev
  simp only [Set.mem_union, Set.mem_setOf_eq]
  exact or_congr Iff.rfl (and_congr ⟨fun h => Sum.inl_injective h, fun h => h ▸ rfl⟩ Iff.rfl)

theorem Formula.sat_embed : ∀ (φ : Formula Voc) (S : Str (Voc.ext L ιL).toSignature) (v : Val Voc) (i : ℕ),
    (φ.embed (L := L) (ιL := ιL)).sat S v i ↔ φ.sat S.restrict v i
  | .top, _, _, _ => Iff.rfl
  | .eq .., _, _, _ => Iff.rfl
  | .pred e ts, S, v, i => by
    simp only [Formula.embed, Formula.sat]
    rw [Term.evalList_embed]
    refine exists_congr fun ds => and_congr_right fun _ => ?_
    constructor
    · rintro ⟨ev, hev, he, ha⟩
      obtain ⟨e', args, har⟩ := ev
      simp only at he ha; subst he ha
      exact ⟨⟨e, args, har⟩, hev, rfl, rfl⟩
    · rintro ⟨ev, hev, rfl, rfl⟩
      exact ⟨_, hev, rfl, rfl⟩
  | .neg φ, S, v, i => by simp only [Formula.embed, Formula.sat, Formula.sat_embed φ]
  | .and φ ψ, S, v, i => by simp only [Formula.embed, Formula.sat, Formula.sat_embed φ, Formula.sat_embed ψ]
  | .ex x φ, S, v, i => by
    simp only [Formula.embed, Formula.sat]
    exact exists_congr fun d => Formula.sat_embed φ S _ i
  | .next I φ, S, v, i => by simp only [Formula.embed, Formula.sat, Formula.sat_embed φ]; rfl
  | .prev I φ, S, v, i => by simp only [Formula.embed, Formula.sat, Formula.sat_embed φ]; rfl
  | .eventually I φ, S, v, i => by simp only [Formula.embed, Formula.sat, Formula.sat_embed φ]; rfl
  | .since I φ ψ, S, v, i => by
    simp only [Formula.embed, Formula.sat, Formula.sat_embed φ, Formula.sat_embed ψ]; rfl
  | .letin e xs φ ψ, S, v, i => by
    simp only [Formula.embed, Formula.sat]
    rw [Formula.sat_embed ψ, Formula.fv_embed]
    have : (fun v' j => (φ.embed (L := L) (ιL := ιL)).sat S v' j) = fun v' j => φ.sat S.restrict v' j := by
      funext v' j; exact propext (Formula.sat_embed φ S v' j)
    rw [this, Str.restrict_extend]
  | .agg ys ω ss gs φ, S, v, i => by
    have key : ∀ v' : Val (Voc.ext L ιL), @Term.evalList (Voc.ext L ιL) v' (Term.embedList ss) =
        @Term.evalList Voc v' ss := fun v' => Term.evalList_embed (Voc := Voc) (L := L) (ιL := ιL) v' ss
    simp only [Formula.embed, Formula.sat, Formula.fv_embed, Formula.sat_embed φ, key]
    rfl

end ext

/-! ## Well-formed sources -/

/-- The source formula is well formed for let-normalization (NOTES.md, "Theorem 4.3 with the let-normal form of Theorem 4.1"):
    every subformula that becomes a let body (`∃`, `●`, `S`, a source `let`)
    is clean w.r.t. its own free variables, a source `let e(x̄) = φ` has
    distinct `x̄ = fv(φ)` of arity `ι(e)`, and aggregations have the arity of
    their operator. -/
def Formula.LnfOK : Formula Voc → Prop
  | .top | .pred .. | .eq .. => True
  | .neg φ | .next _ φ | .eventually _ φ => φ.LnfOK
  | .and φ ψ => φ.LnfOK ∧ ψ.LnfOK
  | .ex x φ => (Formula.ex x φ).Clean (Formula.ex x φ).fv ∧ φ.LnfOK
  | .prev _ φ => φ.Clean φ.fv ∧ φ.LnfOK
  | .since I φ ψ => (Formula.since I φ ψ).Clean (Formula.since I φ ψ).fv ∧ φ.LnfOK ∧ ψ.LnfOK
  | .letin e xs φ ψ => φ.Clean {x | x ∈ xs} ∧ φ.fv = {x | x ∈ xs} ∧ xs.Nodup ∧
      xs.length = Voc.ι e ∧ φ.LnfOK ∧ ψ.LnfOK
  | .agg ys ω _ _ φ => ys.length = (Voc.ι' ω).2 ∧ φ.LnfOK

/-- A let that satisfies the let conditions of `WF`. -/
structure LetGood {W : Vocabulary} (d : LetDef W) : Prop where
  fv : d.φ.fv = {x | x ∈ d.xs}
  nodup : d.xs.Nodup
  arity : d.xs.length = W.ι d.e
  clean : d.φ.Clean {x | x ∈ d.xs}
  warity : d.φ.WellArity
  fun_ok : d.φ.FunOK
  agg : ∀ ys ω ss gs ψ, d.φ = .agg ys ω ss gs ψ → ys.length = (W.ι' ω).2

theorem Formula.Clean.anti {W : Vocabulary} : ∀ {φ : Formula W} {G G' : Set W.𝕍},
    φ.Clean G → G' ⊆ G → φ.Clean G'
  | .top, _, _, _, _ | .pred .., _, _, _, _ | .eq .., _, _, _, _ | .agg .., _, _, _, _ => trivial
  | .neg φ, _, _, h, hG | .next _ φ, _, _, h, hG | .prev _ φ, _, _, h, hG
  | .eventually _ φ, _, _, h, hG | .letin _ _ _ φ, _, _, h, hG => Formula.Clean.anti (φ := φ) h hG
  | .and φ ψ, _, _, h, hG | .since _ φ ψ, _, _, h, hG =>
    ⟨Formula.Clean.anti (φ := φ) h.1 (Set.union_subset_union_left _ hG),
      Formula.Clean.anti (φ := ψ) h.2 (Set.union_subset_union_left _ hG)⟩
  | .ex x φ, _, _, h, hG =>
    ⟨fun h' => h.1 (hG h'), Formula.Clean.anti (φ := φ) h.2 (Set.union_subset_union_left _ hG)⟩

theorem length_embedList {L : Type} [Finite L] {ιL : L → ℕ} :
    ∀ ts : List (Term Voc), (Term.embedList (L := L) (ιL := ιL) ts).length = ts.length
  | [] => rfl
  | _ :: ts => by simp only [Term.embedList, List.length_cons, length_embedList ts]

section good
variable {L : Type} [Finite L] {ιL : L → ℕ} (nm : ℕ → ℕ → L)

theorem predDisj_atoms (ns : List (Voc.ext L ιL).ℰ) (ts : List (Term (Voc.ext L ιL))) :
    (predDisj ns ts).atoms = {a | a.1 ∈ ns ∧ a.2 = ts} := by
  induction ns with
  | nil => ext a; simp [predDisj, Formula.bot, Formula.atoms]
  | cons n ns ih =>
    simp only [predDisj, List.foldr_cons, Formula.or, Formula.atoms] at ih ⊢
    rw [ih]; ext a; obtain ⟨a1, a2⟩ := a; simp [and_comm, or_and_right]

theorem predDisj_clean (ns : List (Voc.ext L ιL).ℰ) (ts : List (Term (Voc.ext L ιL))) (G) :
    (predDisj ns ts).Clean G := by
  induction ns generalizing G with
  | nil => trivial
  | cons n ns ih =>
    simp only [predDisj, List.foldr_cons, Formula.or, Formula.Clean] at ih ⊢
    exact ⟨trivial, ih _⟩

theorem norm_not_agg (φ : Formula Voc) : ∀ ρ (Ls : List (LetDef (Voc.ext L ιL))) ys ω ss gs ψ,
    (norm nm ρ φ Ls).1 ≠ .agg ys ω ss gs ψ := by
  induction φ with
  | letin e xs φ ψ ih₁ ih₂ => intro ρ Ls; exact ih₂ _ _
  | ex x φ ih =>
    intro ρ Ls ys ω ss gs ψ
    simp only [norm]; split_ifs <;> simp [emit]
  | pred e ts =>
    intro ρ Ls ys ω ss gs ψ
    simp only [norm, predDisj, List.foldr_cons, Formula.or]; simp
  | _ => intros; simp [norm, emit]

variable {U : Set Voc.𝕍} {A : ℕ} (hU : U.Finite) (hUA : U.ncard < A)
  (hιA : ∀ e, Voc.ι e < A) (hA : ∀ k a, a < A → ιL (nm k a) = a)
include hU hUA hA

theorem emit_good (β : Formula (Voc.ext L ιL)) (Ls : List (LetDef (Voc.ext L ιL)))
    (hβ : β.fv ⊆ U) (hc : β.Clean β.fv) (hw : β.WellArity) (hf : β.FunOK)
    (hg : ∀ ys ω ss gs ψ, β = .agg ys ω ss gs ψ → ys.length = (Voc.ι' ω).2) :
    LetGood (⟨Sum.inr (nm Ls.length β.fvList.length), β.fvList, β⟩ : LetDef (Voc.ext L ιL)) ∧
      (emit nm β Ls).1.WellArity ∧ (emit nm β Ls).1.FunOK ∧ ∀ G, (emit nm β Ls).1.Clean G := by
  have har := arity_ok nm hU hUA hA β hβ Ls.length
  have hfv : β.fv = {x | x ∈ β.fvList} := by ext x; exact Formula.mem_fvList.symm
  refine ⟨⟨hfv, by simp [Formula.fvList, Finset.nodup_toList], har.symm, hfv ▸ hc, hw, hf, hg⟩,
    ?_, ?_, fun _ => trivial⟩
  · intro a ha
    simp only [emit, Formula.atoms, Set.mem_singleton_iff] at ha; subst ha
    simp only [List.length_map]; exact har.symm
  · intro a ha v hv
    simp only [emit, Formula.atoms, Set.mem_singleton_iff] at ha; subst ha
    simp only [evalList_map_var]
    obtain ⟨ds, hds⟩ := mapM_isSome v β.fvList fun x hx => hv x (by
      simp only [varsList_map_var]; exact hx)
    rw [hds]; rfl

include hιA

/-- **The lets produced by `norm` are good.** -/
theorem norm_good (φ : Formula Voc) : ∀ ρ (Ls : List (LetDef (Voc.ext L ιL))),
    (∀ e f, f ∈ ρ e → ιL f = Voc.ι e) → (∀ d ∈ Ls, LetGood d) →
    φ.LnfOK → φ.WellArity → φ.FunOK → φ.allV ⊆ U →
    (∀ d ∈ (norm nm ρ φ Ls).2, LetGood d) ∧ (norm nm ρ φ Ls).1.WellArity ∧
      (norm nm ρ φ Ls).1.FunOK ∧ ∀ G, φ.Clean G → (norm nm ρ φ Ls).1.Clean G := by
  induction φ with
  | top => intro ρ Ls _ hL _ _ _ _; exact ⟨hL, fun a h => absurd h (Set.notMem_empty _),
      fun a h => absurd h (Set.notMem_empty _), fun _ _ => trivial⟩
  | eq => intro ρ Ls _ hL _ _ _ _; exact ⟨hL, fun a h => absurd h (Set.notMem_empty _),
      fun a h => absurd h (Set.notMem_empty _), fun _ _ => trivial⟩
  | pred e ts =>
    intro ρ Ls hρ hL _ hw hf _
    simp only [norm]
    refine ⟨hL, ?_, ?_, fun G _ => predDisj_clean _ _ G⟩
    · intro a ha
      rw [predDisj_atoms] at ha
      obtain ⟨h1, h2⟩ := ha
      rw [h2, length_embedList, hw (e, ts) rfl]
      simp only [List.mem_cons, List.mem_map] at h1
      rcases h1 with h1 | ⟨f, hf', h1⟩
      · rw [h1]; rfl
      · rw [← h1]; exact (hρ e f hf').symm
    · intro a ha v hv
      rw [predDisj_atoms] at ha
      obtain ⟨-, h2⟩ := ha
      rw [h2] at hv ⊢
      rw [Term.varsList_embed] at hv
      have := Term.evalList_embed (Voc := Voc) (L := L) (ιL := ιL) v ts
      rw [this]
      exact hf (e, ts) rfl v hv
  | neg φ ih | next _ φ ih | eventually _ φ ih =>
    intro ρ Ls hρ hL hok hw hf hU'
    exact ih ρ Ls hρ hL hok hw hf hU'
  | and φ ψ ih₁ ih₂ =>
    intro ρ Ls hρ hL hok hw hf hU'
    obtain ⟨a1, a2, a3, a4⟩ := ih₁ ρ Ls hρ hL hok.1 (WellArity.mono hw Set.subset_union_left)
      (FunOK.mono hf Set.subset_union_left) (Set.subset_union_left.trans hU')
    obtain ⟨b1, b2, b3, b4⟩ := ih₂ ρ _ hρ a1 hok.2 (WellArity.mono hw Set.subset_union_right)
      (FunOK.mono hf Set.subset_union_right) (Set.subset_union_right.trans hU')
    refine ⟨b1, ?_, ?_, fun G hG => ?_⟩
    · rintro a (ha | ha); exacts [a2 a ha, b2 a ha]
    · rintro a (ha | ha); exacts [a3 a ha, b3 a ha]
    · simp only [norm, Formula.Clean, (norm_chi nm φ ρ Ls).2, (norm_chi nm ψ ρ (norm nm ρ φ Ls).2).2]
      exact ⟨a4 _ hG.1, b4 _ hG.2⟩
  | ex x φ ih =>
    intro ρ Ls hρ hL hok hw hf hU'
    obtain ⟨a1, a2, a3, a4⟩ := ih ρ Ls hρ hL hok.2 hw hf (Set.subset_union_right.trans hU')
    have hfvφ := (norm_chi nm φ ρ Ls).2
    simp only [norm]
    split_ifs with hfut
    · exact ⟨a1, a2, a3, fun G hG => ⟨hG.1, a4 _ hG.2⟩⟩
    · have hfvβ : (Formula.ex (Voc := Voc.ext L ιL) x (norm nm ρ φ Ls).1).fv = (Formula.ex x φ).fv := by
        simp only [Formula.fv, hfvφ]; rfl
      obtain ⟨g1, g2, g3, g4⟩ := emit_good nm hU hUA hA (Formula.ex (Voc := Voc.ext L ιL) x (norm nm ρ φ Ls).1)
        (norm nm ρ φ Ls).2 (by rw [hfvβ]; exact Set.subset_union_left.trans hU')
        (by rw [hfvβ]; exact ⟨hok.1.1, a4 _ hok.1.2⟩) a2 a3 (by intros; simp_all)
      refine ⟨fun d hd => ?_, g2, g3, fun G _ => g4 G⟩
      rcases List.mem_append.1 hd with hd | hd
      · exact a1 d hd
      · simp only [List.mem_singleton] at hd; subst hd; exact g1
  | prev I φ ih =>
    intro ρ Ls hρ hL hok hw hf hU'
    obtain ⟨a1, a2, a3, a4⟩ := ih ρ Ls hρ hL hok.2 hw hf hU'
    have hfvφ := (norm_chi nm φ ρ Ls).2
    simp only [norm]
    obtain ⟨g1, g2, g3, g4⟩ := emit_good nm hU hUA hA (Formula.prev I (norm nm ρ φ Ls).1)
      (norm nm ρ φ Ls).2 (by simp only [Formula.fv, hfvφ]; exact (Formula.fv_sub_allV φ).trans hU')
      (by simp only [Formula.fv, Formula.Clean, hfvφ]; exact a4 _ hok.1) a2 a3 (by intros; simp_all)
    refine ⟨fun d hd => ?_, g2, g3, fun G _ => g4 G⟩
    rcases List.mem_append.1 hd with hd | hd
    · exact a1 d hd
    · simp only [List.mem_singleton] at hd; subst hd; exact g1
  | since I φ ψ ih₁ ih₂ =>
    intro ρ Ls hρ hL hok hw hf hU'
    obtain ⟨a1, a2, a3, a4⟩ := ih₁ ρ Ls hρ hL hok.2.1 (WellArity.mono hw Set.subset_union_left)
      (FunOK.mono hf Set.subset_union_left) (Set.subset_union_left.trans hU')
    obtain ⟨b1, b2, b3, b4⟩ := ih₂ ρ _ hρ a1 hok.2.2 (WellArity.mono hw Set.subset_union_right)
      (FunOK.mono hf Set.subset_union_right) (Set.subset_union_right.trans hU')
    have f1 := (norm_chi nm φ ρ Ls).2
    have f2 := (norm_chi nm ψ ρ (norm nm ρ φ Ls).2).2
    simp only [norm]
    obtain ⟨g1, g2, g3, g4⟩ := emit_good nm hU hUA hA
      (Formula.since I (norm nm ρ φ Ls).1 (norm nm ρ ψ (norm nm ρ φ Ls).2).1)
      (norm nm ρ ψ (norm nm ρ φ Ls).2).2
      (by simp only [Formula.fv, f1, f2]
          exact Set.union_subset ((Formula.fv_sub_allV φ).trans (Set.subset_union_left.trans hU'))
            ((Formula.fv_sub_allV ψ).trans (Set.subset_union_right.trans hU')))
      (by simp only [Formula.fv, Formula.Clean, f1, f2]
          exact ⟨a4 _ hok.1.1, b4 _ hok.1.2⟩)
      (by rintro a (ha | ha); exacts [a2 a ha, b2 a ha])
      (by rintro a (ha | ha); exacts [a3 a ha, b3 a ha]) (by intros; simp_all)
    refine ⟨fun d hd => ?_, g2, g3, fun G _ => g4 G⟩
    rcases List.mem_append.1 hd with hd | hd
    · exact b1 d hd
    · simp only [List.mem_singleton] at hd; subst hd; exact g1
  | agg ys ω ss gs φ ih =>
    intro ρ Ls hρ hL hok hw hf hU'
    obtain ⟨a1, a2, a3, a4⟩ := ih ρ Ls hρ hL hok.2 hw hf (Set.subset_union_right.trans hU')
    simp only [norm]
    obtain ⟨g1, g2, g3, g4⟩ := emit_good nm hU hUA hA
      (Formula.agg ys ω (Term.embedList ss) gs (norm nm ρ φ Ls).1) (norm nm ρ φ Ls).2
      (by simp only [Formula.fv]; exact Set.subset_union_left.trans hU') trivial a2 a3
      (by intro ys' ω' ss' gs' ψ' h; cases h; exact hok.1)
    refine ⟨fun d hd => ?_, g2, g3, fun G _ => g4 G⟩
    rcases List.mem_append.1 hd with hd | hd
    · exact a1 d hd
    · simp only [List.mem_singleton] at hd; subst hd; exact g1
  | letin e xs φ ψ ih₁ ih₂ =>
    intro ρ Ls hρ hL hok hw hf hU'
    obtain ⟨hcl, hfv, hnd, hlen, hok₁, hok₂⟩ := hok
    obtain ⟨a1, a2, a3, a4⟩ := ih₁ ρ Ls hρ hL hok₁ (WellArity.mono hw Set.subset_union_left)
      (FunOK.mono hf Set.subset_union_left) (Set.subset_union_left.trans hU')
    have hfvφ := (norm_chi nm φ ρ Ls).2
    simp only [norm]
    apply ih₂ _ _ _ _ hok₂ (WellArity.mono hw Set.subset_union_right)
      (FunOK.mono hf Set.subset_union_right) (Set.subset_union_right.trans hU')
    · intro e' f hf'
      by_cases he : e' = e
      · subst he
        simp only [Function.update_self, List.mem_cons] at hf'
        rcases hf' with rfl | hf'
        · exact hA _ _ (hιA e')
        · exact hρ e' f hf'
      · rw [Function.update_of_ne he] at hf'; exact hρ e' f hf'
    · intro d hd
      rcases List.mem_append.1 hd with hd | hd
      · exact a1 d hd
      · simp only [List.mem_singleton] at hd; subst hd
        refine ⟨by rw [hfvφ, hfv]; rfl, hnd, ?_, a4 _ hcl, a2, a3, fun ys ω ss gs ψ' h =>
          absurd h (norm_not_agg nm φ ρ Ls ys ω ss gs ψ')⟩
        show xs.length = ιL _
        rw [hA _ _ (hιA e)]; exact hlen

end good

/-! ## The let-normal form of Theorem 4.1, with room for obligation names -/

section construction
variable (φ : Formula Voc)

/-- A bound on the arities. -/
noncomputable def lnfA : ℕ := φ.allV.ncard + iSup Voc.ι + 1

/-- Three bands of `|φ| + 1` indices: lets, `Cau_p`, `Sup_p`. -/
def lnfK : ℕ := 3 * (φ.count + 1)

theorem lnfA_pos : 0 < lnfA φ := by unfold lnfA; omega
theorem lnfK_pos : 0 < lnfK φ := by unfold lnfK; omega

/-- The new names. -/
abbrev LN := Fin (lnfK φ) × Fin (lnfA φ)

def ιN : LN φ → ℕ := fun l => l.2.val

noncomputable def nmN : ℕ → ℕ → LN φ := fun k a =>
  (⟨k % lnfK φ, Nat.mod_lt _ (lnfK_pos φ)⟩, ⟨a % lnfA φ, Nat.mod_lt _ (lnfA_pos φ)⟩)

/-- The extended vocabulary. -/
abbrev WN := Voc.ext (LN φ) (ιN φ)

noncomputable def rN : Formula (WN φ) × List (LetDef (WN φ)) :=
  norm (ιL := ιN φ) (nmN φ) (fun _ => []) φ []

/-- **The let-normal form of `□φ`.** -/
noncomputable def lnfN : LNF (WN φ) := ⟨(rN φ).2, [(rN φ).1]⟩

theorem hA_N : ∀ k a, a < lnfA φ → ιN φ (nmN φ k a) = a := fun _ _ ha => Nat.mod_eq_of_lt ha

theorem hιA_N : ∀ e, Voc.ι e < lnfA φ := fun e => by
  haveI := Voc.finE
  have := le_ciSup (Set.finite_range Voc.ι).bddAbove e
  unfold lnfA; omega

theorem hUA_N : φ.allV.ncard < lnfA φ := by unfold lnfA; omega

theorem rN_len : (rN φ).2.length ≤ φ.count := by
  obtain ⟨new, hnew, hcount⟩ := norm_prefix (ιL := ιN φ) (nmN φ) φ (fun _ => []) []
  show (norm _ (fun _ => []) φ []).2.length ≤ φ.count
  rw [hnew]; simpa using hcount

theorem rN_scope : LetsOK (nmN φ) (rN φ).2 ∧
    (rN φ).1.names ⊆ Set.range Sum.inl ∪ LetNames (rN φ).2 :=
  norm_scope (ιL := ιN φ) (nmN φ) φ (fun _ => []) [] (by simp) (by intro k hk; simp at hk)

theorem nmN_fst {k a : ℕ} (hk : k < lnfK φ) : (nmN φ k a).1.val = k := Nat.mod_eq_of_lt hk

theorem rN_inj : ∀ k k' a a', k < (rN φ).2.length → k' < (rN φ).2.length →
    nmN φ k a = nmN φ k' a' → k = k' := by
  intro k k' a a' hk hk' h
  have := congrArg (fun l => l.1.val) h
  have h1 := rN_len φ
  rwa [nmN_fst φ (by unfold lnfK; omega), nmN_fst φ (by unfold lnfK; omega)] at this

/-- The `k`-th let is named `(k, a)`. -/
theorem rN_name {k : ℕ} (hk : k < (rN φ).2.length) :
    ∃ l : LN φ, (rN φ).2[k].e = Sum.inr l ∧ l.1.val = k ∧ k < φ.count := by
  obtain ⟨-, -, a, ha⟩ := (rN_scope φ).1 k hk
  have h1 := rN_len φ
  exact ⟨_, ha, nmN_fst φ (by unfold lnfK; omega), by omega⟩

theorem rN_let_name {e : (WN φ).ℰ} (he : IsLet (rN φ).2 e) :
    ∃ l : LN φ, e = Sum.inr l ∧ l.1.val < φ.count := by
  obtain ⟨d, hd, rfl⟩ := he
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  obtain ⟨l, h1, h2, h3⟩ := rN_name φ hk
  exact ⟨l, h1, h2 ▸ h3⟩

theorem rN_chi : (rN φ).1.IsChi ∧ (rN φ).1.fv = φ.fv := norm_chi (ιL := ιN φ) (nmN φ) φ (fun _ => []) []

/-- **Theorem 4.1 for `lnfN`.** -/
theorem lnfN_valid : (lnfN φ).Valid := by
  refine ⟨?_, by simp [lnfN], ?_⟩
  · intro d hd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    exact ((rN_scope φ).1 k hk).1
  · intro χ hχ; simp [lnfN] at hχ; subst hχ; exact (rN_chi φ).1

theorem lnfN_sem (σ : Str Voc.toSignature) (v : Val Voc) (i : ℕ) (hv : v.Covers φ.fv) :
    (Formula.Always φ).sat σ v i ↔ (lnfN φ).toFormula.sat (Str.embed σ) v i := by
  set r := rN φ
  have hOK := (rN_scope φ).1
  set S := applyLets r.2 (Str.embed σ)
  obtain ⟨hτ, hD0, hDef⟩ := applyLets_spec (nmN φ) r.2 hOK (rN_inj φ) (Str.embed σ)
    (by rintro j ev ⟨ev', -, he, -⟩; exact ⟨_, he.symm⟩) r.2.length le_rfl
  rw [List.take_length] at hτ hD0 hDef
  have hD : ∀ d ∈ r.2, LetDefined S d := by
    intro d hd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    exact hDef k hk hk
  have hR : Rel (fun _ => []) σ S := by
    refine ⟨hτ.symm, fun j e args => ?_⟩
    simp only [List.map_nil, List.mem_singleton, exists_eq_left]
    constructor
    · rintro ⟨ev, hev, he, ha⟩
      refine ⟨⟨Sum.inl e, args, ?_⟩, ?_, rfl, rfl⟩
      · show args.length = Voc.ι e; rw [← ha, ← he]; exact ev.arity
      · rw [hD0 j _ ?_]
        · exact ⟨ev, hev, congrArg Sum.inl he.symm, ha.symm⟩
        · intro k hk _ h
          obtain ⟨-, -, a, ha'⟩ := hOK k hk
          rw [ha'] at h; exact Sum.inl_ne_inr h
    · rintro ⟨ev, hev, he, ha⟩
      rw [hD0 j _ ?_] at hev
      · obtain ⟨ev', hev', he', ha'⟩ := hev
        exact ⟨ev', hev', Sum.inl_injective (he'.symm.trans he), ha'.symm.trans ha⟩
      · intro k hk _ h
        obtain ⟨-, -, a, ha'⟩ := hOK k hk
        rw [he, ha'] at h; exact Sum.inl_ne_inr h
  have hsem := fun j => norm_sem (ιL := ιN φ) (nmN φ) φ.allV_finite (hUA_N φ) (hιA_N φ) (hA_N φ)
    φ (fun _ => []) [] S σ hD hR le_rfl v hv j
  rw [lnfN, toFormula_sat]
  show (Formula.Always φ).sat σ v i ↔ (Formula.Always r.1).sat S v i
  simp only [Formula.Always, Formula.always, Formula.sat]
  rw [hτ]
  refine not_congr (exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ => ?_)
  exact not_congr (hsem j)

end construction

theorem Formula.preds_sub_names {W : Vocabulary} : ∀ φ : Formula W, φ.preds ⊆ φ.names
  | .top => fun _ ⟨_, h, _⟩ => absurd h (Set.notMem_empty _)
  | .eq .. => fun _ ⟨_, h, _⟩ => absurd h (Set.notMem_empty _)
  | .pred e ts => by rintro _ ⟨a, h, rfl⟩; simp only [Formula.atoms, Set.mem_singleton_iff] at h; subst h; rfl
  | .neg φ | .ex _ φ | .next _ φ | .prev _ φ | .eventually _ φ | .agg _ _ _ _ φ => Formula.preds_sub_names φ
  | .and φ ψ | .since _ φ ψ => by
    rintro _ ⟨a, h | h, rfl⟩
    · exact Or.inl (Formula.preds_sub_names φ ⟨a, h, rfl⟩)
    · exact Or.inr (Formula.preds_sub_names ψ ⟨a, h, rfl⟩)
  | .letin e xs φ ψ => by
    rintro _ ⟨a, h | h, rfl⟩
    · exact Or.inl (Or.inr (Formula.preds_sub_names φ ⟨a, h, rfl⟩))
    · exact Or.inr (Formula.preds_sub_names ψ ⟨a, h, rfl⟩)

theorem toFormula_names {W : Vocabulary} (chis : List (Formula W)) (X : Set W.ℰ)
    (hb : (LNF.body ⟨[], chis⟩).names ⊆ X) :
    ∀ Ls : List (LetDef W), (∀ d ∈ Ls, d.e ∈ X ∧ d.φ.names ⊆ X) →
      (LNF.toFormula ⟨Ls, chis⟩).names ⊆ X
  | [], _ => hb
  | d :: Ls, h => by
    have := toFormula_names chis X hb Ls fun d' hd' => h d' (by simp [hd'])
    show ({d.e} ∪ d.φ.names ∪ (LNF.toFormula ⟨Ls, chis⟩).names) ⊆ X
    obtain ⟨h1, h2⟩ := h d (by simp)
    exact Set.union_subset (Set.union_subset (Set.singleton_subset_iff.2 h1) h2) this

section construction
variable (φ : Formula Voc)

/-- The obligation names: `Cau_p` in the second band, `Sup_p` in the third. -/
noncomputable def oblN (b : ℕ) (hb : b ≤ 2) : (WN φ).ℰ → (WN φ).ℰ
  | .inr l => if h : l.1.val ≤ φ.count then
      .inr (⟨b * (φ.count + 1) + l.1.val, by unfold lnfK; nlinarith⟩, l.2)
    else .inr (⟨b * (φ.count + 1), by unfold lnfK; nlinarith⟩, ⟨0, lnfA_pos φ⟩)
  | .inl _ => .inr (⟨b * (φ.count + 1), by unfold lnfK; nlinarith⟩, ⟨0, lnfA_pos φ⟩)

theorem oblN_band (b : ℕ) (hb : b ≤ 2) (p : (WN φ).ℰ) :
    ∃ l : LN φ, oblN φ b hb p = .inr l ∧ b * (φ.count + 1) ≤ l.1.val ∧
      l.1.val ≤ b * (φ.count + 1) + φ.count := by
  cases p with
  | inl e => exact ⟨_, rfl, le_rfl, by simp⟩
  | inr l =>
    simp only [oblN]
    split_ifs with h
    · exact ⟨_, rfl, by simp, by simp; omega⟩
    · exact ⟨_, rfl, le_rfl, by simp⟩

theorem oblN_let (b : ℕ) (hb : b ≤ 2) {l : LN φ} (hl : l.1.val < φ.count) :
    oblN φ b hb (.inr l) = .inr (⟨b * (φ.count + 1) + l.1.val, by unfold lnfK; nlinarith⟩, l.2) := by
  simp only [oblN, dif_pos hl.le]

/-- The names of the let bodies and of `χ` are original names or let names. -/
theorem lnfN_names : ∀ d ∈ (lnfN φ).lets, d.φ.names ⊆ Set.range Sum.inl ∪ LetNames (rN φ).2 := by
  intro d hd
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
  refine ((rN_scope φ).1 k hk).2.1.trans (Set.union_subset_union_right _ ?_)
  rintro _ ⟨d', hd', rfl⟩; exact ⟨d', List.mem_of_mem_take hd', rfl⟩

/-- Names of the extended vocabulary that are neither original nor let names. -/
theorem fresh_of_band {o : (WN φ).ℰ} {l : LN φ} (ho : o = .inr l) (hl : φ.count ≤ l.1.val) :
    o ∉ Set.range Sum.inl ∪ LetNames (rN φ).2 := by
  rintro (⟨e, he⟩ | hL)
  · rw [ho] at he; exact Sum.inl_ne_inr he
  · obtain ⟨l', h1, h2⟩ := rN_let_name φ hL
    rw [ho] at h1; cases h1; omega

variable (Cau Sup base : Set Voc.ℰ) (zero : Voc.𝔻)

/-- The setting of Figure 5 over the extended vocabulary. -/
noncomputable def ΞN : RwSetting (WN φ) :=
  ⟨Sum.inl '' Cau, Sum.inl '' Sup, Sum.inl '' base, oblN φ 1 (by norm_num), oblN φ 2 le_rfl, zero⟩

variable (hcl : φ.Clean ∅) (hok : φ.LnfOK) (hw : φ.WellArity) (hf : φ.FunOK) (hfv : φ.fv = ∅)
include hcl hok hw hf hfv

theorem lnfN_good : (∀ d ∈ (lnfN φ).lets, LetGood d) ∧ (rN φ).1.WellArity ∧ (rN φ).1.FunOK ∧
    (rN φ).1.Clean ∅ := by
  obtain ⟨h1, h2, h3, h4⟩ := norm_good (ιL := ιN φ) (nmN φ) φ.allV_finite (hUA_N φ) (hιA_N φ) (hA_N φ) φ
    (fun _ => []) [] (by simp) (by simp) hok hw hf le_rfl
  exact ⟨h1, h2, h3, h4 ∅ hcl⟩

/-- **`lnfN` is well formed.** -/
theorem lnfN_wf : WF (ΞN φ Cau Sup base zero) φ.embed (lnfN φ) := by
  obtain ⟨hg, hwχ, hfχ, hcχ⟩ := lnfN_good φ hcl hok hw hf hfv
  have hlets : (lnfN φ).lets = (rN φ).2 := rfl
  have hchis : (lnfN φ).chis = [(rN φ).1] := rfl
  have hnotlet : ∀ e, e ∈ Set.range (Sum.inl : Voc.ℰ → (WN φ).ℰ) → ¬ IsLet (lnfN φ).lets e := by
    rintro _ ⟨e, rfl⟩ hl
    obtain ⟨l, h, -⟩ := rN_let_name φ hl; exact Sum.inl_ne_inr h
  have hletinr : ∀ d ∈ (lnfN φ).lets, ∃ l : LN φ, d.e = .inr l ∧ l.1.val < φ.count :=
    fun d hd => rN_let_name φ ⟨d, hd, rfl⟩
  have hpreds : ∀ d ∈ (lnfN φ).lets, d.φ.preds ⊆ Set.range Sum.inl ∪ LetNames (rN φ).2 :=
    fun d hd => (Formula.preds_sub_names _).trans (lnfN_names φ d hd)
  have hχpreds : (rN φ).1.preds ⊆ Set.range Sum.inl ∪ LetNames (rN φ).2 :=
    (Formula.preds_sub_names _).trans (rN_scope φ).2
  refine ⟨?_, ?_, fun d hd => (hg d hd).fv, fun d hd => (hg d hd).arity, fun d hd => (hg d hd).nodup,
    ?_, ?_, ⟨?_, fun d hd => (hg d hd).clean⟩, ⟨fun d hd => (hg d hd).warity, ?_⟩, ?_, ?_, ?_,
    fun d hd => (hg d hd).agg, ⟨fun d hd => (hg d hd).fun_ok, ?_⟩⟩
  · -- distinct let names
    have hf' : (lnfN φ).lets.map (fun d => Sum.elim (fun _ => 0) (fun l : LN φ => l.1.val) d.e) =
        List.range (rN φ).2.length := by
      refine List.ext_getElem (by simp [lnfN]) fun k h1 h2 => ?_
      rw [List.getElem_map, List.getElem_range]
      have hk : k < (rN φ).2.length := by simpa using h2
      obtain ⟨l, hl, hk', -⟩ := rN_name φ hk
      show Sum.elim _ _ ((rN φ).2[k]).e = k
      rw [hl]; exact hk'
    have : ((lnfN φ).lets.map LetDef.e).map (Sum.elim (fun _ => 0) (fun l : LN φ => l.1.val)) =
        List.range (rN φ).2.length := List.map_map.trans hf'
    exact List.Nodup.of_map _ (this ▸ List.nodup_range)
  · intro d hd
    obtain ⟨l, hl, -⟩ := hletinr d hd
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hl]
    · rintro ⟨_, -, h⟩; exact Sum.inl_ne_inr h
    · rintro ⟨_, -, h⟩; exact Sum.inl_ne_inr h
    · rintro ⟨_, -, h⟩; exact Sum.inl_ne_inr h
    · rintro ⟨a, ha, h⟩
      obtain ⟨e, he⟩ := Formula.atoms_embed φ a ha
      exact Sum.inl_ne_inr (he.trans h)
  · -- scope
    intro k hk e he
    rcases ((Formula.preds_sub_names _).trans ((rN_scope φ).1 k hk).2.1) he with he | he
    · exact Or.inl (hnotlet e he)
    · obtain ⟨m, hm, hmk, hme⟩ := mem_LetNames_take he
      exact Or.inr ⟨m, hmk, hm, hme⟩
  · intro χ hχ; rw [hchis] at hχ; simp at hχ; subst hχ; rw [(rN_chi φ).2]; exact hfv
  · intro χ hχ; rw [hchis] at hχ; simp at hχ; subst hχ; exact hcχ
  · intro χ hχ; rw [hchis] at hχ; simp at hχ; subst hχ; exact hwχ
  · -- obligation names are injective on the lets
    rintro p q ⟨d, hd, rfl⟩ ⟨d', hd', rfl⟩
    obtain ⟨l, hl, hlc⟩ := hletinr d hd
    obtain ⟨l', hl', hlc'⟩ := hletinr d' hd'
    simp only [ΞN]
    rw [hl, hl', oblN_let φ 1 _ hlc, oblN_let φ 1 _ hlc', oblN_let φ 2 _ hlc, oblN_let φ 2 _ hlc']
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · injection h with h; injection h with h1 h2; injection h1 with h1
      exact congrArg Sum.inr (Prod.ext (Fin.ext (by omega)) h2)
    · injection h with h; injection h with h1 h2; injection h1 with h1
      exact congrArg Sum.inr (Prod.ext (Fin.ext (by omega)) h2)
    · injection h with h; injection h with h1 h2; injection h1 with h1; omega
  · -- obligation names are fresh
    intro p o ho
    have hband : ∃ l : LN φ, o = .inr l ∧ φ.count ≤ l.1.val := by
      rcases ho with rfl | ho
      · obtain ⟨l, h1, h2, -⟩ := oblN_band φ 1 (by norm_num) p; exact ⟨l, h1, by omega⟩
      · simp only [Set.mem_singleton_iff] at ho; subst ho
        obtain ⟨l, h1, h2, -⟩ := oblN_band φ 2 le_rfl p; exact ⟨l, h1, by omega⟩
    obtain ⟨l, hl, hlc⟩ := hband
    have hfr := fresh_of_band φ hl hlc
    refine ⟨fun h => hfr (Or.inr (by obtain ⟨d, hd, rfl⟩ := h; exact ⟨d, hd, rfl⟩)),
      fun d hd h => hfr (hpreds d hd h), fun χ hχ h => ?_⟩
    rw [hchis] at hχ; simp at hχ; subst hχ; exact hfr (hχpreds h)
  · intro d hd
    obtain ⟨l, hl, hlc⟩ := hletinr d hd
    simp only [ΞN]
    rw [hl, oblN_let φ 1 _ hlc, oblN_let φ 2 _ hlc]
    exact ⟨rfl, rfl⟩
  · intro χ hχ; rw [hchis] at hχ; simp at hχ; subst hχ; exact hfχ

omit hcl hok hw hf in
/-- **`lnfN` is equivalent to `□φ`** on the traces of the extended signature
    without let events. -/
theorem lnfN_equiv : ∀ σ : Trace (WN φ).toSignature, σ.length = ⊤ →
    Admissible {e | IsLet (lnfN φ).lets e} σ →
    ((Formula.Always φ.embed).satTr σ Val.empty 0 ↔ (lnfN φ).toFormula.satTr σ Val.empty 0) := by
  intro σ hσ hadm
  simp only [Formula.satTr, hσ, true_and]
  set S := σ.toStr
  have h1 : (Formula.Always φ.embed).sat S Val.empty 0 ↔
      (Formula.Always φ).sat S.restrict Val.empty 0 := Formula.sat_embed (Formula.Always φ) S _ _
  have h2 := lnfN_sem φ S.restrict Val.empty 0 (by rw [hfv]; intro x hx; exact absurd hx (Set.notMem_empty _))
  have hnames : (lnfN φ).toFormula.names ⊆ Set.range Sum.inl ∪ LetNames (rN φ).2 :=
    toFormula_names [(rN φ).1] _ (rN_scope φ).2 (rN φ).2
      fun d hd => ⟨Or.inr ⟨d, hd, rfl⟩, lnfN_names φ d hd⟩
  have hagree : (Str.embed S.restrict).Agree S (lnfN φ).toFormula.names := by
    refine ⟨rfl, fun j ev he => ?_⟩
    rcases hnames he with ⟨e, he'⟩ | hl
    · constructor
      · rintro ⟨ev', hev', h1, h2⟩
        have : ev = ⟨Sum.inl ev'.e, ev'.args, ev'.arity⟩ := Event.ext h1 h2
        rw [this]; exact hev'
      · intro hev
        refine ⟨⟨e, ev.args, ?_⟩, ?_, he'.symm, rfl⟩
        · have := ev.arity; rw [← he'] at this; exact this
        · show (⟨Sum.inl e, ev.args, _⟩ : Event (WN φ).toSignature) ∈ S.D j
          have : ev = ⟨Sum.inl e, ev.args, by have := ev.arity; rw [← he'] at this; exact this⟩ :=
            Event.ext he'.symm rfl
          rw [← this]; exact hev
    · obtain ⟨l, hl', -⟩ := rN_let_name φ (by obtain ⟨d, hd, h⟩ := hl; exact ⟨d, hd, h⟩)
      constructor
      · rintro ⟨ev', -, h1, -⟩; rw [hl'] at h1; exact absurd h1.symm Sum.inl_ne_inr
      · intro hev
        exact absurd (by obtain ⟨d, hd, h⟩ := hl; exact ⟨d, hd, h⟩) (hadm j ev hev)
  exact h1.trans (h2.trans (Formula.sat_agree _ _ _ _ _ hagree))

end construction

/-- **Theorem 4.3 with the let-normal form of Theorem 4.1** (NOTES.md, "Theorem 4.3 with the let-normal form of Theorem 4.1"):
    for a closed, clean, well-formed MFOTL formula `φ`, the hypotheses of
    `Theorem_4_3` on the let-normal form (validity, `WF`, equivalence) hold
    for `lnfN φ` with the obligation names `oblN`, so the compiled program is
    a sound enforcer for `□φ` whenever Algorithm 3, the checks of §4.5 and
    Algorithm 4 succeed. -/
theorem theorem_4_3_lnf (φ : Formula Voc) (hm : φ.IsMFOTL) (hfv : φ.fv = ∅) (hcl : φ.Clean ∅)
    (hok : φ.LnfOK) (hw : φ.WellArity) (hf : φ.FunOK) (Cau Sup base : Set Voc.ℰ) (zero : Voc.𝔻) :
    let Ξ := ΞN φ Cau Sup base zero
    let L := lnfN φ
    ∀ T, TypeLets Ξ L.lets = some T →
    ∀ R, (∃ 𝒞, Rw Ξ T.Γ .C (bigAnd L.chis) 𝒞 ∧ ∃ C ∈ 𝒞, R ∈ Realizations Ξ T C) →
    ConflictCheck L.lets R → (∃ O, DFGCheck O L.lets R) →
    ∀ rk, TopoOrder L.lets R rk →
    ∀ rs : List (EClause (WN φ)), (∀ c, c ∈ rs ↔ c ∈ R) →
    ∀ evTys colTy P, Compile Ξ L.lets T.Γ rs rk evTys colTy = some P →
      P.SoundEnforcer (Ξ.Cau ∪ Set.range Ξ.cauN ∪ Set.range Ξ.supN) Ξ.Sup
        (Admissible (NewNames Ξ L.lets)) (Formula.Always φ.embed) := by
  intro Ξ L
  exact theorem_4_3 Ξ (fun _ => L) φ.embed (Formula.isMFOTL_embed hm)
    (by rw [Formula.fv_embed]; exact hfv) (lnfN_valid φ) (lnfN_wf φ Cau Sup base zero hcl hok hw hf hfv)
    (lnfN_equiv φ hfv)

end Paper
