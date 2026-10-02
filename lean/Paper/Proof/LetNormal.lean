/-
  Proof of Theorem 4.1 (let-normal form), over a signature extended with
  fresh let names (NOTES.md, N7).
-/
import Paper.Claims
import Paper.Generate
import Paper.Proof.Guards

namespace Paper

variable {Voc : Vocabulary}

/-! ## Coincidence: only the free variables matter -/

mutual
theorem Term.eval_congr (v w : Val Voc) :
    ∀ t : Term Voc, (∀ x ∈ t.vars, v x = w x) → t.eval v = t.eval w
  | .var x, h => h x rfl
  | .const _, _ => rfl
  | .app f ts, h => by
    simp only [Term.eval]
    rw [Term.evalList_congr v w ts h]
theorem Term.evalList_congr (v w : Val Voc) :
    ∀ ts : List (Term Voc), (∀ x ∈ Term.varsList ts, v x = w x) →
      Term.evalList v ts = Term.evalList w ts
  | [], _ => rfl
  | t :: ts, h => by
    simp only [Term.evalList]
    rw [Term.eval_congr v w t (fun x hx => h x (Or.inl hx)),
      Term.evalList_congr v w ts (fun x hx => h x (Or.inr hx))]
end

theorem Formula.sat_congr (φ : Formula Voc) :
    ∀ (σ : Str Voc.toSignature) (v w : Val Voc) (i : ℕ), (∀ x ∈ φ.fv, v x = w x) →
      (φ.sat σ v i ↔ φ.sat σ w i) := by
  induction φ with
  | top => intros; rfl
  | pred e ts =>
    intro σ v w i h
    simp only [Formula.sat]; rw [Term.evalList_congr v w ts h]
  | neg φ ih => intro σ v w i h; simp only [Formula.sat]; rw [ih σ v w i h]
  | and φ ψ ih₁ ih₂ =>
    intro σ v w i h; simp only [Formula.sat]
    rw [ih₁ σ v w i (fun x hx => h x (Or.inl hx)), ih₂ σ v w i (fun x hx => h x (Or.inr hx))]
  | ex x φ ih =>
    intro σ v w i h; simp only [Formula.sat]
    refine exists_congr fun d => ih σ _ _ i fun y hy => ?_
    by_cases hyx : y = x
    · subst hyx; simp [Val.upd]
    · simp only [Val.upd, Function.update_of_ne hyx]; exact h y ⟨hy, hyx⟩
  | next I φ ih => intro σ v w i h; simp only [Formula.sat]; rw [ih σ v w _ h]
  | prev I φ ih => intro σ v w i h; simp only [Formula.sat]; rw [ih σ v w _ h]
  | eventually I φ ih =>
    intro σ v w i h; simp only [Formula.sat]; exact exists_congr fun j => by rw [ih σ v w j h]
  | since I φ ψ ih₁ ih₂ =>
    intro σ v w i h; simp only [Formula.sat]
    refine exists_congr fun j => ?_
    simp only [ih₁ σ v w _ (fun x hx => h x (Or.inl hx)), ih₂ σ v w _ (fun x hx => h x (Or.inr hx))]
  | letin e xs φ ψ _ ih₂ => intro σ v w i h; exact ih₂ _ v w i h
  | agg ys ω ss gs φ _ =>
    intro σ v w i h
    have hg : gs.map v = gs.map w := List.map_congr_left fun x hx => h x (Or.inl hx)
    have hy : ys.map v = ys.map w := List.map_congr_left fun x hx => h x (Or.inr hx)
    simp only [Formula.sat, hg, hy]
  | eq x c => intro σ v w i h; simp only [Formula.sat]; rw [h x rfl]

/-! ## Locality: only the event names that occur matter -/

/-- The event names occurring in a formula (predicates and let names). -/
def Formula.names : Formula Voc → Set Voc.ℰ
  | .top => ∅
  | .pred e _ => {e}
  | .neg φ => φ.names
  | .and φ ψ => φ.names ∪ ψ.names
  | .ex _ φ => φ.names
  | .next _ φ => φ.names
  | .prev _ φ => φ.names
  | .eventually _ φ => φ.names
  | .since _ φ ψ => φ.names ∪ ψ.names
  | .letin e _ φ ψ => {e} ∪ φ.names ∪ ψ.names
  | .agg _ _ _ _ φ => φ.names
  | .eq _ _ => ∅

/-- Two structures agree on the names `N`. -/
def Str.Agree (S S' : Str Voc.toSignature) (N : Set Voc.ℰ) : Prop :=
  S.τ = S'.τ ∧ ∀ j ev, ev.e ∈ N → (ev ∈ S.D j ↔ ev ∈ S'.D j)

theorem Str.Agree.mono {S S' : Str Voc.toSignature} {N N' : Set Voc.ℰ} (h : S.Agree S' N)
    (hN : N' ⊆ N) : S.Agree S' N' := ⟨h.1, fun j ev he => h.2 j ev (hN he)⟩

theorem Formula.sat_agree (φ : Formula Voc) :
    ∀ (S S' : Str Voc.toSignature) (v : Val Voc) (i : ℕ), S.Agree S' φ.names →
      (φ.sat S v i ↔ φ.sat S' v i) := by
  induction φ with
  | top => intros; rfl
  | pred e ts =>
    intro S S' v i h
    simp only [Formula.sat]
    refine exists_congr fun ds => and_congr_right fun _ => ?_
    constructor
    · rintro ⟨ev, hev, he, ha⟩; exact ⟨ev, (h.2 i ev (by simp [Formula.names, he])).1 hev, he, ha⟩
    · rintro ⟨ev, hev, he, ha⟩; exact ⟨ev, (h.2 i ev (by simp [Formula.names, he])).2 hev, he, ha⟩
  | neg φ ih => intro S S' v i h; simp only [Formula.sat]; rw [ih S S' v i h]
  | and φ ψ ih₁ ih₂ =>
    intro S S' v i h; simp only [Formula.sat]
    rw [ih₁ S S' v i (h.mono fun _ hx => Or.inl hx), ih₂ S S' v i (h.mono fun _ hx => Or.inr hx)]
  | ex x φ ih => intro S S' v i h; simp only [Formula.sat]; exact exists_congr fun d => ih S S' _ i h
  | next I φ ih => intro S S' v i h; simp only [Formula.sat]; rw [ih S S' v _ h, h.1]
  | prev I φ ih => intro S S' v i h; simp only [Formula.sat]; rw [ih S S' v _ h, h.1]
  | eventually I φ ih =>
    intro S S' v i h; simp only [Formula.sat]
    exact exists_congr fun j => by rw [ih S S' v j h, h.1]
  | since I φ ψ ih₁ ih₂ =>
    intro S S' v i h; simp only [Formula.sat]
    refine exists_congr fun j => ?_
    simp only [ih₁ S S' v _ (h.mono fun _ hx => Or.inl hx), ih₂ S S' v _ (h.mono fun _ hx => Or.inr hx), h.1]
  | letin e xs φ ψ ih₁ ih₂ =>
    intro S S' v i h
    simp only [Formula.sat]
    apply ih₂
    refine ⟨h.1, fun j ev hev => ?_⟩
    have hφ : ∀ v' j, φ.sat S v' j ↔ φ.sat S' v' j := fun v' j =>
      ih₁ S S' v' j (h.mono fun _ hx => Or.inl (Or.inr hx))
    simp only [Str.extend, Set.mem_union, Set.mem_setOf_eq, hφ]
    rw [h.2 j ev (Or.inr hev)]
  | agg ys ω ss gs φ ih =>
    intro S S' v i h
    have hG : ∀ v', φ.sat S v' i ↔ φ.sat S' v' i := fun v' => ih S S' v' i h
    simp only [Formula.sat, hG]
  | eq x c => intros; rfl


/-! ## Finiteness of free variables -/

mutual
theorem Term.vars_finite : ∀ t : Term Voc, t.vars.Finite
  | .var _ => Set.finite_singleton _
  | .const _ => Set.finite_empty
  | .app _ ts => Term.varsList_finite ts
theorem Term.varsList_finite : ∀ ts : List (Term Voc), (Term.varsList ts).Finite
  | [] => Set.finite_empty
  | t :: ts => (Term.vars_finite t).union (Term.varsList_finite ts)
end

theorem Formula.fv_finite (φ : Formula Voc) : φ.fv.Finite := by
  induction φ with
  | top => exact Set.finite_empty
  | pred _ ts => exact Term.varsList_finite ts
  | neg _ ih => exact ih
  | and _ _ ih₁ ih₂ => exact ih₁.union ih₂
  | ex _ _ ih => exact ih.sdiff
  | next _ _ ih => exact ih
  | prev _ _ ih => exact ih
  | eventually _ _ ih => exact ih
  | since _ _ _ ih₁ ih₂ => exact ih₁.union ih₂
  | letin _ _ _ _ _ ih₂ => exact ih₂
  | agg ys _ _ gs _ _ => exact (List.finite_toSet gs).union (List.finite_toSet ys)
  | eq _ _ => exact Set.finite_singleton _

/-- The free variables as a list (without duplicates). -/
noncomputable def Formula.fvList (φ : Formula Voc) : List Voc.𝕍 := φ.fv_finite.toFinset.toList

theorem Formula.mem_fvList {φ : Formula Voc} {x : Voc.𝕍} : x ∈ φ.fvList ↔ x ∈ φ.fv := by
  simp [Formula.fvList]

theorem Formula.length_fvList (φ : Formula Voc) : φ.fvList.length = φ.fv.ncard := by
  simp [Formula.fvList, Set.ncard_eq_toFinset_card _ φ.fv_finite]

/-! ## Embedding into the extended signature -/

section ext
variable {L : Type} [Finite L] {ιL : L → ℕ}

mutual
theorem Term.eval_embed (v : Val Voc) :
    ∀ t : Term Voc, @Term.eval (Voc.ext L ιL) v (Term.embed t) = t.eval v
  | .var _ => rfl
  | .const _ => rfl
  | .app f ts => by
    simp only [Term.embed, Term.eval]
    rw [Term.evalList_embed v ts]; rfl
theorem Term.evalList_embed (v : Val Voc) :
    ∀ ts : List (Term Voc), @Term.evalList (Voc.ext L ιL) v (Term.embedList ts) = Term.evalList v ts
  | [] => rfl
  | t :: ts => by
    simp only [Term.embedList, Term.evalList]
    rw [Term.eval_embed v t, Term.evalList_embed v ts]; rfl
end

mutual
theorem Term.vars_embed : ∀ t : Term Voc, (Term.embed (L := L) (ιL := ιL) t).vars = t.vars
  | .var _ => rfl
  | .const _ => rfl
  | .app f ts => by simp only [Term.embed, Term.vars]; exact Term.varsList_embed ts
theorem Term.varsList_embed :
    ∀ ts : List (Term Voc), Term.varsList (Term.embedList (L := L) (ιL := ιL) ts) = Term.varsList ts
  | [] => rfl
  | t :: ts => by
    simp only [Term.embedList, Term.varsList]
    rw [Term.vars_embed t, Term.varsList_embed ts]; rfl
end

end ext

/-! ## The normalization -/

/-- Number of let-producing nodes (a bound on the number of lets). -/
def Formula.count : Formula Voc → ℕ
  | .top | .pred _ _ | .eq _ _ => 0
  | .neg φ | .next _ φ | .eventually _ φ => φ.count
  | .and φ ψ => φ.count + ψ.count
  | .ex _ φ | .prev _ φ | .agg _ _ _ _ φ => φ.count + 1
  | .since _ φ ψ | .letin _ _ φ ψ => φ.count + ψ.count + 1

/-- All free variables of all subformulas. -/
def Formula.allV : Formula Voc → Set Voc.𝕍
  | .top => ∅
  | .pred _ ts => Term.varsList ts
  | .eq x _ => {x}
  | .neg φ | .next _ φ | .eventually _ φ | .prev _ φ => φ.allV
  | .ex x φ => (φ.fv \ {x}) ∪ φ.allV
  | .and φ ψ | .since _ φ ψ => φ.allV ∪ ψ.allV
  | .agg ys _ _ gs φ => {x | x ∈ gs} ∪ {x | x ∈ ys} ∪ φ.allV
  | .letin _ _ φ ψ => φ.allV ∪ ψ.allV

theorem Formula.fv_sub_allV (φ : Formula Voc) : φ.fv ⊆ φ.allV := by
  induction φ with
  | top | pred | eq => exact le_rfl
  | neg _ ih | next _ _ ih | eventually _ _ ih | prev _ _ ih => exact ih
  | ex x φ _ => exact Set.subset_union_left
  | and _ _ ih₁ ih₂ | since _ _ _ ih₁ ih₂ => exact Set.union_subset_union ih₁ ih₂
  | agg => exact Set.subset_union_left
  | letin _ _ _ _ _ ih₂ => exact ih₂.trans Set.subset_union_right

theorem Formula.allV_finite (φ : Formula Voc) : φ.allV.Finite := by
  induction φ with
  | top => exact Set.finite_empty
  | pred _ ts => exact Term.varsList_finite ts
  | eq => exact Set.finite_singleton _
  | neg _ ih | next _ _ ih | eventually _ _ ih | prev _ _ ih => exact ih
  | ex x φ ih => exact (φ.fv_finite.sdiff).union ih
  | and _ _ ih₁ ih₂ | since _ _ _ ih₁ ih₂ | letin _ _ _ _ ih₁ ih₂ => exact ih₁.union ih₂
  | agg ys _ _ gs _ ih => exact ((List.finite_toSet gs).union (List.finite_toSet ys)).union ih

section norm
open Classical
variable {L : Type} [Finite L] {ιL : L → ℕ} (nm : ℕ → ℕ → L)

/-- `⋁_{n ∈ ns} n(t̄)` -/
def predDisj (ns : List (Voc.ext L ιL).ℰ) (ts : List (Term (Voc.ext L ιL))) :
    Formula (Voc.ext L ιL) :=
  ns.foldr (fun n φ => Formula.or (.pred n ts) φ) .bot

/-- Bind `β` to a fresh let `f(fv(β))` (the `k`-th let, `k = |Ls|`) and return
    the atom `f(fv(β))`. -/
noncomputable def emit (β : Formula (Voc.ext L ιL)) (Ls : List (LetDef (Voc.ext L ιL))) :
    Formula (Voc.ext L ιL) × List (LetDef (Voc.ext L ιL)) :=
  (.pred (Sum.inr (nm Ls.length β.fvList.length)) (β.fvList.map Term.var),
    Ls ++ [⟨Sum.inr (nm Ls.length β.fvList.length), β.fvList, β⟩])

/-- Let-normalization.  `ρ e` lists the fresh names of the source lets binding
    `e` in scope; an atom `e(t̄)` becomes `e(t̄) ∨ ⋁_{f ∈ ρ e} f(t̄)`, since
    `σ[e ↦ φ]` adds `e`-events (Figure 1). -/
noncomputable def norm : (Voc.ℰ → List L) → Formula Voc → List (LetDef (Voc.ext L ιL)) →
    Formula (Voc.ext L ιL) × List (LetDef (Voc.ext L ιL))
  | _, .top, Ls => (.top, Ls)
  | _, .eq x c, Ls => (.eq x c, Ls)
  | ρ, .pred e ts, Ls => (predDisj (Sum.inl e :: (ρ e).map Sum.inr) (Term.embedList ts), Ls)
  | ρ, .neg φ, Ls => ((norm ρ φ Ls).1.neg, (norm ρ φ Ls).2)
  | ρ, .and φ ψ, Ls =>
    (.and (norm ρ φ Ls).1 (norm ρ ψ (norm ρ φ Ls).2).1, (norm ρ ψ (norm ρ φ Ls).2).2)
  | ρ, .next I φ, Ls => (.next I (norm ρ φ Ls).1, (norm ρ φ Ls).2)
  | ρ, .eventually I φ, Ls => (.eventually I (norm ρ φ Ls).1, (norm ρ φ Ls).2)
  | ρ, .ex x φ, Ls =>
    if (norm ρ φ Ls).1.HasFuture then (.ex x (norm ρ φ Ls).1, (norm ρ φ Ls).2)
    else emit nm (.ex x (norm ρ φ Ls).1) (norm ρ φ Ls).2
  | ρ, .prev I φ, Ls => emit nm (.prev I (norm ρ φ Ls).1) (norm ρ φ Ls).2
  | ρ, .since I φ ψ, Ls =>
    emit nm (.since I (norm ρ φ Ls).1 (norm ρ ψ (norm ρ φ Ls).2).1) (norm ρ ψ (norm ρ φ Ls).2).2
  | ρ, .agg ys ω ss gs φ, Ls =>
    emit nm (.agg ys ω (Term.embedList ss) gs (norm ρ φ Ls).1) (norm ρ φ Ls).2
  | ρ, .letin e xs φ ψ, Ls =>
    norm (Function.update ρ e (nm (norm ρ φ Ls).2.length (Voc.ι e) :: ρ e)) ψ
      ((norm ρ φ Ls).2 ++ [⟨Sum.inr (nm (norm ρ φ Ls).2.length (Voc.ι e)), xs, (norm ρ φ Ls).1⟩])


theorem varsList_map_var (xs : List (Voc.ext L ιL).𝕍) :
    Term.varsList (xs.map Term.var) = {x | x ∈ xs} := by
  induction xs with
  | nil => simp [Term.varsList]
  | cons x xs ih =>
    simp only [List.map_cons, Term.varsList, Term.vars, ih]
    ext y; simp [eq_comm]

theorem predDisj_fv (ns : List (Voc.ext L ιL).ℰ) (ts : List (Term (Voc.ext L ιL))) (h : ns ≠ []) :
    (predDisj ns ts).fv = Term.varsList ts := by
  induction ns with
  | nil => exact absurd rfl h
  | cons n ns ih =>
    cases ns with
    | nil => simp [predDisj, Formula.or, Formula.bot, Formula.fv]
    | cons m ms =>
      have := ih (by simp)
      simp only [predDisj, List.foldr_cons] at this ⊢
      simp only [Formula.or, Formula.fv] at this ⊢
      rw [this]; simp

theorem predDisj_chi (ns : List (Voc.ext L ιL).ℰ) (ts : List (Term (Voc.ext L ιL))) :
    (predDisj ns ts).IsChi := by
  induction ns with
  | nil => trivial
  | cons n ns ih =>
    simp only [predDisj, List.foldr_cons, Formula.or, Formula.IsChi] at ih ⊢
    exact ⟨trivial, ih⟩

theorem emit_fst_fv (β : Formula (Voc.ext L ιL)) (Ls) : (emit nm β Ls).1.fv = β.fv := by
  simp only [emit, Formula.fv, varsList_map_var]
  ext x; exact Formula.mem_fvList

theorem emit_spec (β : Formula (Voc.ext L ιL)) (Ls : List (LetDef (Voc.ext L ιL))) :
    ∃ d, (emit nm β Ls).2 = Ls ++ [d] := ⟨_, rfl⟩

theorem norm_prefix (φ : Formula Voc) : ∀ ρ (Ls : List (LetDef (Voc.ext L ιL))), ∃ new,
    (norm nm ρ φ Ls).2 = Ls ++ new ∧ new.length ≤ φ.count := by
  induction φ with
  | top | eq | pred => intro ρ Ls; exact ⟨[], by simp [norm], by simp⟩
  | neg φ ih | next _ φ ih | eventually _ φ ih =>
    intro ρ Ls; obtain ⟨n, h, hl⟩ := ih ρ Ls
    exact ⟨n, by simp only [norm]; exact h, by simpa [Formula.count] using hl⟩
  | and φ ψ ih₁ ih₂ =>
    intro ρ Ls
    obtain ⟨n₁, h₁, l₁⟩ := ih₁ ρ Ls
    obtain ⟨n₂, h₂, l₂⟩ := ih₂ ρ (norm nm ρ φ Ls).2
    refine ⟨n₁ ++ n₂, ?_, by simp [Formula.count]; omega⟩
    simp only [norm]; rw [h₂, h₁, List.append_assoc]
  | ex x φ ih =>
    intro ρ Ls; obtain ⟨n, h, hl⟩ := ih ρ Ls
    simp only [norm]
    split_ifs
    · exact ⟨n, h, by simp [Formula.count]; omega⟩
    · obtain ⟨d, hd⟩ := emit_spec nm (.ex x (norm nm ρ φ Ls).1) (norm nm ρ φ Ls).2
      exact ⟨n ++ [d], by rw [hd, h, List.append_assoc], by simp [Formula.count]; omega⟩
  | prev I φ ih =>
    intro ρ Ls; obtain ⟨n, h, hl⟩ := ih ρ Ls
    obtain ⟨d, hd⟩ := emit_spec nm (.prev I (norm nm ρ φ Ls).1) (norm nm ρ φ Ls).2
    exact ⟨n ++ [d], by simp only [norm]; rw [hd, h, List.append_assoc], by simp [Formula.count]; omega⟩
  | agg ys ω ss gs φ ih =>
    intro ρ Ls; obtain ⟨n, h, hl⟩ := ih ρ Ls
    obtain ⟨d, hd⟩ := emit_spec nm (.agg ys ω (Term.embedList ss) gs (norm nm ρ φ Ls).1) (norm nm ρ φ Ls).2
    exact ⟨n ++ [d], by simp only [norm]; rw [hd, h, List.append_assoc], by simp [Formula.count]; omega⟩
  | since I φ ψ ih₁ ih₂ =>
    intro ρ Ls
    obtain ⟨n₁, h₁, l₁⟩ := ih₁ ρ Ls
    obtain ⟨n₂, h₂, l₂⟩ := ih₂ ρ (norm nm ρ φ Ls).2
    obtain ⟨d, hd⟩ := emit_spec nm (.since I (norm nm ρ φ Ls).1 (norm nm ρ ψ (norm nm ρ φ Ls).2).1)
      (norm nm ρ ψ (norm nm ρ φ Ls).2).2
    refine ⟨n₁ ++ n₂ ++ [d], ?_, by simp [Formula.count]; omega⟩
    simp only [norm]; rw [hd, h₂, h₁]; simp
  | letin e xs φ ψ ih₁ ih₂ =>
    intro ρ Ls
    obtain ⟨n₁, h₁, l₁⟩ := ih₁ ρ Ls
    obtain ⟨n₂, h₂, l₂⟩ := ih₂ (Function.update ρ e (nm (norm nm ρ φ Ls).2.length (Voc.ι e) :: ρ e))
      ((norm nm ρ φ Ls).2 ++ [⟨Sum.inr (nm (norm nm ρ φ Ls).2.length (Voc.ι e)), xs, (norm nm ρ φ Ls).1⟩])
    refine ⟨n₁ ++ [⟨Sum.inr (nm (norm nm ρ φ Ls).2.length (Voc.ι e)), xs, (norm nm ρ φ Ls).1⟩] ++ n₂,
      ?_, by simp [Formula.count]; omega⟩
    simp only [norm]; rw [h₂]
    exact (congrArg (fun l => l ++ _ ++ n₂) h₁).trans (by simp)

theorem norm_chi (φ : Formula Voc) : ∀ ρ (Ls : List (LetDef (Voc.ext L ιL))),
    (norm nm ρ φ Ls).1.IsChi ∧ (norm nm ρ φ Ls).1.fv = φ.fv := by
  induction φ with
  | top | eq => intro ρ Ls; exact ⟨trivial, rfl⟩
  | pred e ts =>
    intro ρ Ls
    refine ⟨predDisj_chi _ _, ?_⟩
    simp only [norm]; rw [predDisj_fv _ _ (by simp), Term.varsList_embed]; rfl
  | neg φ ih => intro ρ Ls; exact ih ρ Ls
  | next _ φ ih | eventually _ φ ih => intro ρ Ls; exact ih ρ Ls
  | and φ ψ ih₁ ih₂ =>
    intro ρ Ls
    obtain ⟨c₁, f₁⟩ := ih₁ ρ Ls; obtain ⟨c₂, f₂⟩ := ih₂ ρ (norm nm ρ φ Ls).2
    exact ⟨⟨c₁, c₂⟩, by simp only [norm, Formula.fv, f₁, f₂]; rfl⟩
  | ex x φ ih =>
    intro ρ Ls; obtain ⟨c, f⟩ := ih ρ Ls
    simp only [norm]
    split_ifs with hf
    · exact ⟨⟨hf, c⟩, by simp only [Formula.fv, f]; rfl⟩
    · exact ⟨trivial, by rw [emit_fst_fv]; simp only [Formula.fv, f]; rfl⟩
  | prev I φ ih =>
    intro ρ Ls; obtain ⟨c, f⟩ := ih ρ Ls
    exact ⟨trivial, by simp only [norm]; rw [emit_fst_fv]; simp only [Formula.fv, f]⟩
  | agg ys ω ss gs φ ih =>
    intro ρ Ls
    exact ⟨trivial, by simp only [norm]; rw [emit_fst_fv]; rfl⟩
  | since I φ ψ ih₁ ih₂ =>
    intro ρ Ls
    obtain ⟨c₁, f₁⟩ := ih₁ ρ Ls; obtain ⟨c₂, f₂⟩ := ih₂ ρ (norm nm ρ φ Ls).2
    exact ⟨trivial, by simp only [norm]; rw [emit_fst_fv]; simp only [Formula.fv, f₁, f₂]; rfl⟩
  | letin e xs φ ψ ih₁ ih₂ =>
    intro ρ Ls
    exact ih₂ _ _


/-- The names bound by a list of lets. -/
def LetNames (Ls : List (LetDef (Voc.ext L ιL))) : Set (Voc.ext L ιL).ℰ := {n | ∃ d ∈ Ls, d.e = n}

/-- The `k`-th let is a let body in let-normal form, mentions only base events
    and earlier lets, and is named `nm k a` for some `a`. -/
def LetsOK (Ls : List (LetDef (Voc.ext L ιL))) : Prop :=
  ∀ k (h : k < Ls.length), Ls[k].φ.IsLetBody ∧
    Ls[k].φ.names ⊆ Set.range Sum.inl ∪ LetNames (Ls.take k) ∧ ∃ a, Ls[k].e = Sum.inr (nm k a)

theorem LetsOK.snoc {Ls : List (LetDef (Voc.ext L ιL))} {d : LetDef (Voc.ext L ιL)}
    (h : LetsOK nm Ls) (h₁ : d.φ.IsLetBody) (h₂ : d.φ.names ⊆ Set.range Sum.inl ∪ LetNames Ls)
    (h₃ : ∃ a, d.e = Sum.inr (nm Ls.length a)) : LetsOK nm (Ls ++ [d]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  by_cases hkl : k < Ls.length
  · rw [List.getElem_append_left hkl, List.take_append_of_le_length hkl.le]
    exact h k hkl
  · have hk' : k = Ls.length := by omega
    subst hk'
    simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_singleton,
      List.take_left]
    exact ⟨h₁, h₂, h₃⟩

theorem LetNames_mono {Ls new : List (LetDef (Voc.ext L ιL))} : LetNames Ls ⊆ LetNames (Ls ++ new) :=
  fun _ ⟨d, hd, he⟩ => ⟨d, List.mem_append_left _ hd, he⟩

theorem predDisj_names (ns : List (Voc.ext L ιL).ℰ) (ts : List (Term (Voc.ext L ιL))) :
    (predDisj ns ts).names = {n | n ∈ ns} := by
  induction ns with
  | nil => simp [predDisj, Formula.bot, Formula.names]
  | cons n ns ih =>
    simp only [predDisj, List.foldr_cons, Formula.or, Formula.names] at ih ⊢
    rw [ih]; ext m; simp [eq_comm]

theorem emit_scope (β : Formula (Voc.ext L ιL)) (Ls : List (LetDef (Voc.ext L ιL)))
    (hL : LetsOK nm Ls) (hβ : β.IsLetBody) (hn : β.names ⊆ Set.range Sum.inl ∪ LetNames Ls) :
    LetsOK nm (emit nm β Ls).2 ∧
      (emit nm β Ls).1.names ⊆ Set.range Sum.inl ∪ LetNames (emit nm β Ls).2 := by
  refine ⟨hL.snoc nm hβ hn ⟨_, rfl⟩, ?_⟩
  intro n hn'
  simp only [emit, Formula.names, Set.mem_singleton_iff] at hn'
  subst hn'
  exact Or.inr ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

theorem norm_scope (φ : Formula Voc) : ∀ ρ (Ls : List (LetDef (Voc.ext L ιL))),
    (∀ e f, f ∈ ρ e → Sum.inr f ∈ LetNames Ls) → LetsOK nm Ls →
    LetsOK nm (norm nm ρ φ Ls).2 ∧
      (norm nm ρ φ Ls).1.names ⊆ Set.range Sum.inl ∪ LetNames (norm nm ρ φ Ls).2 := by
  induction φ with
  | top => intro ρ Ls _ hL; exact ⟨hL, by simp [norm, Formula.names]⟩
  | eq => intro ρ Ls _ hL; exact ⟨hL, by simp [norm, Formula.names]⟩
  | pred e ts =>
    intro ρ Ls hρ hL
    refine ⟨hL, ?_⟩
    simp only [norm]; rw [predDisj_names]
    intro n hn
    simp only [Set.mem_setOf_eq, List.mem_cons, List.mem_map] at hn
    rcases hn with rfl | ⟨f, hf, rfl⟩
    · exact Or.inl ⟨e, rfl⟩
    · exact Or.inr (hρ e f hf)
  | neg φ ih | next _ φ ih | eventually _ φ ih => intro ρ Ls hρ hL; exact ih ρ Ls hρ hL
  | and φ ψ ih₁ ih₂ =>
    intro ρ Ls hρ hL
    obtain ⟨L₁, n₁⟩ := ih₁ ρ Ls hρ hL
    obtain ⟨new, hnew, _⟩ := norm_prefix nm φ ρ Ls
    obtain ⟨new₂, hnew₂, _⟩ := norm_prefix nm ψ ρ (norm nm ρ φ Ls).2
    obtain ⟨L₂, n₂⟩ := ih₂ ρ (norm nm ρ φ Ls).2
      (fun e f hf => by rw [hnew]; exact LetNames_mono (hρ e f hf)) L₁
    refine ⟨L₂, ?_⟩
    simp only [norm, Formula.names]
    refine Set.union_subset (n₁.trans ?_) n₂
    rw [hnew₂]; exact Set.union_subset_union_right _ LetNames_mono
  | ex x φ ih =>
    intro ρ Ls hρ hL
    obtain ⟨L₁, n₁⟩ := ih ρ Ls hρ hL
    have c := (norm_chi nm φ ρ Ls).1
    simp only [norm]
    split_ifs with hf
    · exact ⟨L₁, n₁⟩
    · exact emit_scope nm _ _ L₁ (Or.inl ⟨[x], _, rfl, c⟩) n₁
  | prev I φ ih =>
    intro ρ Ls hρ hL
    obtain ⟨L₁, n₁⟩ := ih ρ Ls hρ hL
    have c := (norm_chi nm φ ρ Ls).1
    exact emit_scope nm _ _ L₁ (Or.inr (Or.inl ⟨I, _, rfl, [], _, rfl, c⟩)) n₁
  | agg ys ω ss gs φ ih =>
    intro ρ Ls hρ hL
    obtain ⟨L₁, n₁⟩ := ih ρ Ls hρ hL
    have c := (norm_chi nm φ ρ Ls).1
    exact emit_scope nm _ _ L₁ (Or.inr (Or.inr (Or.inr ⟨ys, ω, _, gs, _, rfl, [], _, rfl, c⟩))) n₁
  | since I φ ψ ih₁ ih₂ =>
    intro ρ Ls hρ hL
    obtain ⟨L₁, n₁⟩ := ih₁ ρ Ls hρ hL
    obtain ⟨new, hnew, _⟩ := norm_prefix nm φ ρ Ls
    obtain ⟨new₂, hnew₂, _⟩ := norm_prefix nm ψ ρ (norm nm ρ φ Ls).2
    obtain ⟨L₂, n₂⟩ := ih₂ ρ (norm nm ρ φ Ls).2
      (fun e f hf => by rw [hnew]; exact LetNames_mono (hρ e f hf)) L₁
    have c₁ := (norm_chi nm φ ρ Ls).1
    have c₂ := (norm_chi nm ψ ρ (norm nm ρ φ Ls).2).1
    refine emit_scope nm _ _ L₂ (Or.inr (Or.inr (Or.inl ⟨I, _, _, rfl, ⟨[], _, rfl, c₁⟩,
      ⟨[], _, rfl, c₂⟩⟩))) ?_
    simp only [Formula.names]
    refine Set.union_subset (n₁.trans ?_) n₂
    rw [hnew₂]; exact Set.union_subset_union_right _ LetNames_mono
  | letin e xs φ ψ ih₁ ih₂ =>
    intro ρ Ls hρ hL
    obtain ⟨L₁, n₁⟩ := ih₁ ρ Ls hρ hL
    obtain ⟨new, hnew, _⟩ := norm_prefix nm φ ρ Ls
    have c := (norm_chi nm φ ρ Ls).1
    simp only [norm]
    apply ih₂
    · intro e' f hf
      by_cases he : e' = e
      · subst he
        simp only [Function.update_self, List.mem_cons] at hf
        rcases hf with rfl | hf
        · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
        · rw [hnew]; exact LetNames_mono (LetNames_mono (hρ e' f hf))
      · rw [Function.update_of_ne he] at hf
        rw [hnew]; exact LetNames_mono (LetNames_mono (hρ e' f hf))
    · exact L₁.snoc nm (Or.inl ⟨[], _, rfl, c⟩) n₁ ⟨_, rfl⟩


/-! ### Semantics -/

/-- The events named like the let `d` are exactly those `d` defines. -/
def LetDefined (S : Str (Voc.ext L ιL).toSignature) (d : LetDef (Voc.ext L ιL)) : Prop :=
  ∀ j (ev : Event (Voc.ext L ιL).toSignature), ev.e = d.e →
    (ev ∈ S.D j ↔ ∃ v' : Val (Voc.ext L ιL), v'.Covers d.φ.fv ∧ d.xs.map v' = ev.args.map some ∧
      d.φ.sat S v' j)

/-- `T` (over `Voc`, with the source lets in scope) and `S` (over the extended
    vocabulary) agree: an `e`-event of `T` is an `e`-event or an `f`-event of
    `S` for a fresh name `f ∈ ρ e`. -/
def Rel (ρ : Voc.ℰ → List L) (T : Str Voc.toSignature) (S : Str (Voc.ext L ιL).toSignature) : Prop :=
  T.τ = S.τ ∧ ∀ j (e : Voc.ℰ) (args : List Voc.𝔻),
    (∃ ev ∈ T.D j, ev.e = e ∧ ev.args = args) ↔
      ∃ n ∈ (Sum.inl e :: (ρ e).map Sum.inr), ∃ ev ∈ S.D j, ev.e = n ∧ ev.args = args

theorem mapM_eq_some {α β : Type} (f : α → Option β) (xs : List α) (ds : List β) :
    xs.mapM f = some ds ↔ xs.map f = ds.map some := by
  induction xs generalizing ds with
  | nil => cases ds <;> simp
  | cons x xs ih =>
    cases ds with
    | nil =>
      simp only [List.mapM_cons, List.map_cons, List.map_nil, reduceCtorEq, iff_false]
      cases f x <;> simp
      cases List.mapM f xs <;> simp
    | cons d ds =>
      simp only [List.mapM_cons, List.map_cons, List.cons.injEq]
      rw [← ih]
      cases hfx : f x <;> cases hm : List.mapM f xs <;> simp

theorem mapM_isSome {α β : Type} (f : α → Option β) (xs : List α) (h : ∀ x ∈ xs, (f x).isSome) :
    ∃ ds, xs.mapM f = some ds := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 (h x (by simp))
    obtain ⟨ds, hds⟩ := ih (fun y hy => h y (by simp [hy]))
    exact ⟨d :: ds, by simp [hd, hds]⟩

theorem evalList_map_var {W : Vocabulary} (v : Val W) (xs : List W.𝕍) :
    Term.evalList v (xs.map Term.var) = xs.mapM v := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Term.evalList, Term.eval, List.mapM_cons, ih]

theorem sat_predDisj (ns : List (Voc.ext L ιL).ℰ) (ts : List (Term (Voc.ext L ιL)))
    (S : Str (Voc.ext L ιL).toSignature) (v : Val (Voc.ext L ιL)) (i : ℕ) :
    (predDisj ns ts).sat S v i ↔ ∃ n ∈ ns, (Formula.pred n ts).sat S v i := by
  induction ns with
  | nil => simp [predDisj]
  | cons n ns ih =>
    simp only [predDisj, List.foldr_cons, sat_or] at ih ⊢
    rw [ih]; simp

theorem event_exists {Sig : Signature} (e : Sig.ℰ) (args : List Sig.𝔻) :
    (∃ ev : Event Sig, ev.e = e ∧ ev.args = args) ↔ args.length = Sig.ι e :=
  ⟨fun ⟨ev, he, ha⟩ => he ▸ ha ▸ ev.arity, fun h => ⟨⟨e, args, h⟩, rfl, rfl⟩⟩

theorem emit_sat (β : Formula (Voc.ext L ιL)) (Ls : List (LetDef (Voc.ext L ιL)))
    (S : Str (Voc.ext L ιL).toSignature)
    (hd : LetDefined S ⟨Sum.inr (nm Ls.length β.fvList.length), β.fvList, β⟩)
    (har : ιL (nm Ls.length β.fvList.length) = β.fvList.length)
    (v : Val (Voc.ext L ιL)) (hv : v.Covers β.fv) (i : ℕ) :
    (emit nm β Ls).1.sat S v i ↔ β.sat S v i := by
  simp only [emit, Formula.sat, evalList_map_var]
  constructor
  · rintro ⟨ds, hds, ev, hev, he, ha⟩
    obtain ⟨v', -, hv', hs⟩ := (hd i ev he).1 hev
    rw [ha, ← (mapM_eq_some _ _ _).1 hds] at hv'
    refine (Formula.sat_congr β S v' v i fun x hx => ?_).1 hs
    have hx' : x ∈ β.fvList := Formula.mem_fvList.2 hx
    exact (List.map_inj_left.1 hv') x hx'
  · intro hs
    obtain ⟨ds, hds⟩ := mapM_isSome v β.fvList fun x hx => hv x (Formula.mem_fvList.1 hx)
    have hlen : ds.length = β.fvList.length := by
      have := congrArg List.length ((mapM_eq_some _ _ _).1 hds); simpa using this.symm
    refine ⟨ds, hds, ⟨Sum.inr (nm Ls.length β.fvList.length), ds, ?_⟩, ?_, rfl, rfl⟩
    · show ds.length = ιL _; rw [har, hlen]
    · exact (hd i _ rfl).2 ⟨v, hv, (mapM_eq_some _ _ _).1 hds, hs⟩


theorem Val.Covers.upd {W : Vocabulary} {v : Val W} {X : Set W.𝕍} {x : W.𝕍} (h : v.Covers (X \ {x}))
    (d : W.𝔻) : (v.upd x d).Covers X := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; simp [Val.upd]
  · simp only [Val.upd, Function.update_of_ne hyx]; exact h y ⟨hy, hyx⟩

theorem mem_norm_of_mem {φ : Formula Voc} {ρ} {Ls : List (LetDef (Voc.ext L ιL))} {d}
    (h : d ∈ Ls) : d ∈ (norm nm ρ φ Ls).2 := by
  obtain ⟨n, hn, _⟩ := norm_prefix nm φ ρ Ls
  rw [hn]; exact List.mem_append_left _ h

theorem emit_last (β : Formula (Voc.ext L ιL)) (Ls : List (LetDef (Voc.ext L ιL))) :
    (⟨Sum.inr (nm Ls.length β.fvList.length), β.fvList, β⟩ : LetDef _) ∈ (emit nm β Ls).2 :=
  List.mem_append_right _ (List.mem_singleton_self _)

theorem emit_mem {β : Formula (Voc.ext L ιL)} {Ls : List (LetDef (Voc.ext L ιL))} {d}
    (h : d ∈ Ls) : d ∈ (emit nm β Ls).2 := List.mem_append_left _ h

section sem
variable {U : Set Voc.𝕍} {A : ℕ} (hU : U.Finite) (hUA : U.ncard < A)
  (hιA : ∀ e, Voc.ι e < A) (hA : ∀ k a, a < A → ιL (nm k a) = a)
include hU hUA hA

theorem arity_ok (β : Formula (Voc.ext L ιL)) (hβ : β.fv ⊆ U) (k : ℕ) :
    ιL (nm k β.fvList.length) = β.fvList.length := by
  apply hA
  rw [Formula.length_fvList]
  exact lt_of_le_of_lt (Set.ncard_le_ncard hβ hU) hUA

include hιA

theorem norm_sem (φ : Formula Voc) :
    ∀ ρ (Ls : List (LetDef (Voc.ext L ιL))) (S : Str (Voc.ext L ιL).toSignature)
      (T : Str Voc.toSignature),
      (∀ d ∈ (norm nm ρ φ Ls).2, LetDefined S d) → Rel ρ T S → φ.allV ⊆ U →
      ∀ v : Val Voc, v.Covers φ.fv → ∀ i, (φ.sat T v i ↔ (norm nm ρ φ Ls).1.sat S v i) := by
  induction φ with
  | top => intros; exact Iff.rfl
  | eq => intros; exact Iff.rfl
  | pred e ts =>
    intro ρ Ls S T _ hR _ v _ i
    simp only [norm]; rw [sat_predDisj]
    simp only [Formula.sat]
    rw [Term.evalList_embed]
    constructor
    · rintro ⟨ds, hds, h⟩
      obtain ⟨n, hn, h'⟩ := (hR.2 i e ds).1 h
      exact ⟨n, hn, ds, hds, h'⟩
    · rintro ⟨n, hn, ds, hds, h'⟩
      exact ⟨ds, hds, (hR.2 i e ds).2 ⟨n, hn, h'⟩⟩
  | neg φ ih =>
    intro ρ Ls S T hD hR hUφ v hv i
    simp only [norm, Formula.sat]; rw [ih ρ Ls S T hD hR hUφ v hv i]
  | and φ ψ ih₁ ih₂ =>
    intro ρ Ls S T hD hR hUφ v hv i
    simp only [norm] at hD ⊢; simp only [Formula.sat]
    rw [ih₁ ρ Ls S T (fun d hd => hD d (mem_norm_of_mem nm hd)) hR
        (fun x hx => hUφ (Or.inl hx)) v (fun x hx => hv x (Or.inl hx)) i,
      ih₂ ρ _ S T hD hR (fun x hx => hUφ (Or.inr hx)) v (fun x hx => hv x (Or.inr hx)) i]
  | next I φ ih =>
    intro ρ Ls S T hD hR hUφ v hv i
    simp only [norm, Formula.sat]; rw [ih ρ Ls S T hD hR hUφ v hv, hR.1]
  | eventually I φ ih =>
    intro ρ Ls S T hD hR hUφ v hv i
    simp only [norm, Formula.sat]
    exact exists_congr fun j => by rw [ih ρ Ls S T hD hR hUφ v hv, hR.1]
  | ex x φ ih =>
    intro ρ Ls S T hD hR hUφ v hv i
    have hfv := (norm_chi nm φ ρ Ls).2
    simp only [norm] at hD ⊢
    have hUφ' : φ.allV ⊆ U := fun y hy => hUφ (Or.inr hy)
    split_ifs at hD ⊢ with hf
    · simp only [Formula.sat]
      exact exists_congr fun d => ih ρ Ls S T hD hR hUφ' _ (hv.upd d) i
    · rw [emit_sat nm _ _ S (hD _ (emit_last nm _ _))
        (arity_ok nm hU hUA hA _ (by
          show (norm nm ρ φ Ls).1.fv \ {x} ⊆ U
          rw [hfv]; exact fun y hy => hUφ (Or.inl hy)) _)
        v (by show v.Covers ((norm nm ρ φ Ls).1.fv \ {x}); rw [hfv]; exact hv) i]
      simp only [Formula.sat]
      exact exists_congr fun d => ih ρ Ls S T (fun d hd => hD d (emit_mem nm hd)) hR hUφ' _ (hv.upd d) i
  | prev I φ ih =>
    intro ρ Ls S T hD hR hUφ v hv i
    have hfv := (norm_chi nm φ ρ Ls).2
    simp only [norm] at hD ⊢
    rw [emit_sat nm _ _ S (hD _ (emit_last nm _ _))
      (arity_ok nm hU hUA hA _ (by
        show (norm nm ρ φ Ls).1.fv ⊆ U
        rw [hfv]; exact (Formula.fv_sub_allV φ).trans hUφ) _)
      v (by show v.Covers (norm nm ρ φ Ls).1.fv; rw [hfv]; exact hv) i]
    simp only [Formula.sat]
    rw [ih ρ Ls S T (fun d hd => hD d (emit_mem nm hd)) hR hUφ v hv, hR.1]
  | since I φ ψ ih₁ ih₂ =>
    intro ρ Ls S T hD hR hUφ v hv i
    have hfv₁ := (norm_chi nm φ ρ Ls).2
    have hfv₂ := (norm_chi nm ψ ρ (norm nm ρ φ Ls).2).2
    simp only [norm] at hD ⊢
    have hD₂ : ∀ d ∈ (norm nm ρ ψ (norm nm ρ φ Ls).2).2, LetDefined S d :=
      fun d hd => hD d (emit_mem nm hd)
    have hD₁ : ∀ d ∈ (norm nm ρ φ Ls).2, LetDefined S d :=
      fun d hd => hD₂ d (mem_norm_of_mem nm hd)
    rw [emit_sat nm _ _ S (hD _ (emit_last nm _ _))
      (arity_ok nm hU hUA hA _ (by
        show (norm nm ρ φ Ls).1.fv ∪ (norm nm ρ ψ (norm nm ρ φ Ls).2).1.fv ⊆ U
        rw [hfv₁, hfv₂]
        exact Set.union_subset_union (Formula.fv_sub_allV φ) (Formula.fv_sub_allV ψ) |>.trans hUφ) _)
      v (by
        show v.Covers ((norm nm ρ φ Ls).1.fv ∪ (norm nm ρ ψ (norm nm ρ φ Ls).2).1.fv)
        rw [hfv₁, hfv₂]; exact hv) i]
    simp only [Formula.sat]
    refine exists_congr fun j => ?_
    simp only [ih₁ ρ Ls S T hD₁ hR (fun y hy => hUφ (Or.inl hy)) v (fun x hx => hv x (Or.inl hx)),
      ih₂ ρ _ S T hD₂ hR (fun y hy => hUφ (Or.inr hy)) v (fun x hx => hv x (Or.inr hx)), hR.1]
  | agg ys ω ss gs φ ih =>
    intro ρ Ls S T hD hR hUφ v hv i
    have hfv := (norm_chi nm φ ρ Ls).2
    simp only [norm] at hD ⊢
    rw [emit_sat nm _ _ S (hD _ (emit_last nm _ _))
      (arity_ok nm hU hUA hA (.agg ys ω (Term.embedList ss) gs (norm nm ρ φ Ls).1)
        (by intro y hy; exact hUφ (Or.inl hy)) _) v hv i]
    have key : ∀ v' : Val Voc, (∀ x, (v' x).isSome ↔ x ∈ φ.fv) →
        (φ.sat T v' i ↔ (norm nm ρ φ Ls).1.sat S v' i) := fun v' hv' =>
      ih ρ Ls S T (fun d hd => hD d (emit_mem nm hd)) hR (fun y hy => hUφ (Or.inr hy)) v'
        (fun x hx => (hv' x).2 hx) i
    have hset : {v' : Val Voc | (∀ x, (v' x).isSome ↔ x ∈ φ.fv) ∧ gs.map v' = gs.map v ∧
          φ.sat T v' i} =
        {v' : Val Voc | (∀ x, (v' x).isSome ↔ x ∈ (norm nm ρ φ Ls).1.fv) ∧ gs.map v' = gs.map v ∧
          (norm nm ρ φ Ls).1.sat S v' i} := by
      ext v'
      simp only [Set.mem_setOf_eq, hfv]
      exact ⟨fun ⟨a, b, c⟩ => ⟨a, b, (key v' a).1 c⟩, fun ⟨a, b, c⟩ => ⟨a, b, (key v' a).2 c⟩⟩
    have hfun : ∀ v' : Val Voc,
        @Term.evalList (Voc.ext L ιL) v' (Term.embedList ss) = Term.evalList v' ss :=
      fun v' => Term.evalList_embed v' ss
    simp only [Formula.sat]
    rw [hset]
    simp only [hfun]
    exact Iff.rfl
  | letin e xs φ ψ ih₁ ih₂ =>
    intro ρ Ls S T hD hR hUφ v hv i
    have hfv := (norm_chi nm φ ρ Ls).2
    simp only [norm] at hD ⊢
    simp only [Formula.sat]
    set f := nm (norm nm ρ φ Ls).2.length (Voc.ι e) with hf
    set χφ := (norm nm ρ φ Ls).1
    have hDf : LetDefined S ⟨Sum.inr f, xs, χφ⟩ :=
      hD _ (mem_norm_of_mem nm (List.mem_append_right _ (List.mem_singleton_self _)))
    have hD₁ : ∀ d ∈ (norm nm ρ φ Ls).2, LetDefined S d :=
      fun d hd => hD d (mem_norm_of_mem nm (List.mem_append_left _ hd))
    have hφ : ∀ v' j, v'.Covers φ.fv → (φ.sat T v' j ↔ χφ.sat S v' j) := fun v' j hv' =>
      ih₁ ρ Ls S T hD₁ hR (fun y hy => hUφ (Or.inl hy)) v' hv' j
    have harf : ιL f = Voc.ι e := hA _ _ (hιA e)
    apply ih₂ _ _ S _ hD _ (fun y hy => hUφ (Or.inr hy)) v hv i
    refine ⟨hR.1, fun j e' args => ?_⟩
    by_cases he : e' = e
    · subst he
      simp only [Function.update_self, List.map_cons, List.mem_cons, Str.extend, Set.mem_union,
        Set.mem_setOf_eq]
      have old := hR.2 j e' args
      constructor
      · rintro ⟨ev, hev | ⟨he1, v', hv', hxs, hs⟩, he2, ha⟩
        · obtain ⟨n, hn, h⟩ := old.1 ⟨ev, hev, he2, ha⟩
          simp only [List.mem_cons] at hn
          rcases hn with hn | hn
          · exact ⟨n, Or.inl hn, h⟩
          · exact ⟨n, Or.inr (Or.inr hn), h⟩
        · subst ha
          refine ⟨Sum.inr f, Or.inr (Or.inl rfl), ⟨Sum.inr f, ev.args, ?_⟩, ?_, rfl, rfl⟩
          · show ev.args.length = ιL f; rw [harf]; exact he2 ▸ ev.arity
          · refine (hDf j _ rfl).2 ⟨v', by rw [hfv]; exact hv', hxs, ?_⟩
            exact (hφ v' j hv').1 hs
      · rintro ⟨n, hn | hn | hn, ev, hev, he2, ha⟩
        · obtain ⟨ev', h1, h2, h3⟩ := old.2 ⟨n, by simp [hn], ev, hev, he2, ha⟩
          exact ⟨ev', Or.inl h1, h2, h3⟩
        · subst hn
          obtain ⟨v', hv', hxs, hs⟩ := (hDf j ev he2).1 hev
          rw [hfv] at hv'
          subst ha
          refine ⟨⟨e', ev.args, ?_⟩, Or.inr ⟨rfl, v', hv', hxs, (hφ v' j hv').2 hs⟩, rfl, rfl⟩
          rw [← harf]; have := ev.arity; rw [he2] at this; exact this
        · obtain ⟨ev', h1, h2, h3⟩ := old.2 ⟨n, by simp [hn], ev, hev, he2, ha⟩
          exact ⟨ev', Or.inl h1, h2, h3⟩
    · simp only [Function.update_of_ne he, Str.extend, Set.mem_union, Set.mem_setOf_eq]
      rw [← hR.2 j e' args]
      constructor
      · rintro ⟨ev, hev | ⟨he1, _⟩, he2, ha⟩
        · exact ⟨ev, hev, he2, ha⟩
        · exact absurd (he2.symm.trans he1) he
      · rintro ⟨ev, hev, he2, ha⟩
        exact ⟨ev, Or.inl hev, he2, ha⟩

end sem

/-! ### The lets of an LNF build the structure -/

/-- Apply the lets in order (the semantics of nested `let … in`). -/
def applyLets {W : Vocabulary} (Ls : List (LetDef W)) (S : Str W.toSignature) : Str W.toSignature :=
  Ls.foldl (fun S d => S.extend d.e d.xs d.φ.fv (fun v' j => d.φ.sat S v' j)) S

theorem toFormula_sat {W : Vocabulary} (Ls : List (LetDef W)) (chis : List (Formula W)) :
    ∀ (S : Str W.toSignature) v i,
      (LNF.toFormula ⟨Ls, chis⟩).sat S v i ↔ (LNF.body ⟨Ls, chis⟩).sat (applyLets Ls S) v i := by
  induction Ls with
  | nil => intros; rfl
  | cons d Ls ih =>
    intro S v i
    exact ih _ v i

theorem LetsOK.names_ne {Ls : List (LetDef (Voc.ext L ιL))} (hL : LetsOK nm Ls)
    (hinj : ∀ k k' a a', k < Ls.length → k' < Ls.length → nm k a = nm k' a' → k = k')
    {k m : ℕ} (hk : k < Ls.length) (hm : m < Ls.length) (hne : k ≠ m) : Ls[k].e ≠ Ls[m].e := by
  obtain ⟨-, -, a, ha⟩ := hL k hk
  obtain ⟨-, -, b, hb⟩ := hL m hm
  rw [ha, hb]; intro h
  exact hne (hinj k m a b hk hm (Sum.inr_injective h))

theorem mem_LetNames_take {Ls : List (LetDef (Voc.ext L ιL))} {k : ℕ} {n} :
    n ∈ LetNames (Ls.take k) → ∃ m, ∃ hm : m < Ls.length, m < k ∧ Ls[m].e = n := by
  rintro ⟨d, hd, rfl⟩
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hd
  rw [List.length_take] at hm
  exact ⟨m, by omega, by omega, by simp⟩

theorem applyLets_spec (Ls : List (LetDef (Voc.ext L ιL))) (hL : LetsOK nm Ls)
    (hinj : ∀ k k' a a', k < Ls.length → k' < Ls.length → nm k a = nm k' a' → k = k')
    (S₀ : Str (Voc.ext L ιL).toSignature) (h₀ : ∀ j, ∀ ev ∈ S₀.D j, ev.e ∈ Set.range Sum.inl) :
    ∀ n ≤ Ls.length, (applyLets (Ls.take n) S₀).τ = S₀.τ ∧
      (∀ j ev, (∀ k (hk : k < Ls.length), k < n → ev.e ≠ Ls[k].e) →
        (ev ∈ (applyLets (Ls.take n) S₀).D j ↔ ev ∈ S₀.D j)) ∧
      ∀ k (hk : k < Ls.length), k < n → LetDefined (applyLets (Ls.take n) S₀) Ls[k] := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, fun _ _ _ => Iff.rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn
    obtain ⟨iτ, iD, iDef⟩ := ih (by omega)
    have hnl : n < Ls.length := by omega
    set d := Ls[n] with hd
    set Sn := applyLets (Ls.take n) S₀
    have hstep : applyLets (Ls.take (n + 1)) S₀ =
        Sn.extend d.e d.xs d.φ.fv (fun v' j => d.φ.sat Sn v' j) := by
      simp only [applyLets, Sn, List.take_add_one, List.getElem?_eq_getElem hnl, Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil, d]
    rw [hstep]
    -- the new let's name differs from the names of the earlier lets and of base events
    have hdinr : ∃ a, d.e = Sum.inr (nm n a) := (hL n hnl).2.2
    have hnot : ∀ m (hm : m < Ls.length), m < n → Ls[m].e ≠ d.e := fun m hm hmn =>
      hL.names_ne nm hinj hm hnl (by omega)
    -- `Sn` and the extension agree on every name other than `d.e`
    have hagree : ∀ N : Set (Voc.ext L ιL).ℰ, d.e ∉ N →
        Sn.Agree (Sn.extend d.e d.xs d.φ.fv (fun v' j => d.φ.sat Sn v' j)) N := by
      intro N hN
      refine ⟨rfl, fun j ev hev => ?_⟩
      simp only [Str.extend, Set.mem_union, Set.mem_setOf_eq]
      constructor
      · exact Or.inl
      · rintro (h | ⟨he, _⟩)
        · exact h
        · exact absurd (he ▸ hev) hN
    -- the names a let body mentions do not include later let names
    have hscope : ∀ k (hk : k < Ls.length), k ≤ n → d.e ∉ Ls[k].φ.names ∨ k = n := by
      intro k hk hkn
      rcases Nat.lt_or_eq_of_le hkn with hlt | heq
      · left
        intro hmem
        rcases (hL k hk).2.1 hmem with ⟨b, hb⟩ | hmem'
        · obtain ⟨a, ha⟩ := hdinr; rw [ha] at hb; exact Sum.inl_ne_inr hb
        · obtain ⟨m, hm, hmk, hme⟩ := mem_LetNames_take hmem'
          exact hnot m hm (by omega) hme
      · exact Or.inr heq
    have hself : d.e ∉ d.φ.names := by
      intro hmem
      rcases (hL n hnl).2.1 hmem with ⟨b, hb⟩ | hmem'
      · obtain ⟨a, ha⟩ := hdinr; rw [ha] at hb; exact Sum.inl_ne_inr hb
      · obtain ⟨m, hm, hmk, hme⟩ := mem_LetNames_take hmem'
        exact hnot m hm hmk hme
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
        have hn' : d.e ∉ Ls[k].φ.names := by
          rcases hscope k hk hlt.le with h | h
          · exact h
          · omega
        refine exists_congr fun v' => and_congr_right fun _ => and_congr_right fun _ => ?_
        exact Formula.sat_agree _ _ _ _ _ (hagree _ hn')
      · subst heq
        intro j ev he
        simp only [Str.extend, Set.mem_union, Set.mem_setOf_eq]
        have h0 : ev ∉ Sn.D j := by
          intro hev
          rw [iD j ev (fun m hm hmn => he ▸ hnot m hm hmn |>.symm)] at hev
          obtain ⟨b, hb⟩ := h₀ j ev hev
          obtain ⟨a, ha⟩ := hdinr
          rw [he, ha] at hb; exact Sum.inl_ne_inr hb
        constructor
        · rintro (h | ⟨-, v', hv', hxs, hs⟩)
          · exact absurd h h0
          · exact ⟨v', hv', hxs, (Formula.sat_agree _ _ _ _ _ (hagree _ hself)).1 hs⟩
        · rintro ⟨v', hv', hxs, hs⟩
          exact Or.inr ⟨he, v', hv', hxs, (Formula.sat_agree _ _ _ _ _ (hagree _ hself)).2 hs⟩

end norm

/-! ## Theorem 4.1 -/

theorem theorem_4_1 : Theorem_4_1 Voc := by
  intro φ _
  classical
  haveI : Fintype Voc.ℰ := @Fintype.ofFinite _ Voc.finE
  set U := φ.allV
  set A := U.ncard + Finset.univ.sup Voc.ι + 1
  set K := φ.count + 1
  have hA0 : 0 < A := by omega
  have hK0 : 0 < K := by omega
  let nm : ℕ → ℕ → Fin K × Fin A := fun k a => (⟨k % K, Nat.mod_lt _ hK0⟩, ⟨a % A, Nat.mod_lt _ hA0⟩)
  let ιL : Fin K × Fin A → ℕ := fun l => l.2.val
  have hA : ∀ k a, a < A → ιL (nm k a) = a := fun k a ha => Nat.mod_eq_of_lt ha
  have hιA : ∀ e, Voc.ι e < A := fun e => by
    have := Finset.le_sup (f := Voc.ι) (Finset.mem_univ e); omega
  have hUA : U.ncard < A := by omega
  have hU : U.Finite := φ.allV_finite
  let r := norm (ιL := ιL) nm (fun _ => []) φ []
  obtain ⟨new, hnew, hcount⟩ := norm_prefix (ιL := ιL) nm φ (fun _ => []) []
  have hlen : r.2.length ≤ φ.count := by
    show (norm nm (fun _ => []) φ []).2.length ≤ φ.count
    rw [hnew]; simpa using hcount
  obtain ⟨hOK, -⟩ := norm_scope (ιL := ιL) nm φ (fun _ => []) [] (by simp) (by intro k hk; simp at hk)
  have hinj : ∀ k k' a a', k < r.2.length → k' < r.2.length → nm k a = nm k' a' → k = k' := by
    intro k k' a a' hk hk' h
    have := congrArg (fun l => l.1.val) h
    simp only [nm, Nat.mod_eq_of_lt (show k < K by omega), Nat.mod_eq_of_lt (show k' < K by omega)] at this
    exact this
  obtain ⟨hchi, hfv⟩ := norm_chi (ιL := ιL) nm φ (fun _ => []) []
  refine ⟨Fin K × Fin A, inferInstance, ιL, ⟨r.2, [r.1]⟩, ⟨?_, by simp, ?_⟩, ?_, ?_⟩
  · intro d hd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    exact (hOK k hk).1
  · intro χ hχ; simp at hχ; subst hχ; exact hchi
  · intro d hd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    obtain ⟨-, -, a, ha⟩ := hOK k hk
    exact ⟨_, ha⟩
  · intro σ v i hv
    set S := applyLets r.2 (Str.embed σ)
    obtain ⟨hτ, hD0, hDef⟩ := applyLets_spec nm r.2 hOK hinj (Str.embed σ)
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
    have hsem := fun j => norm_sem (ιL := ιL) nm hU hUA hιA hA φ (fun _ => []) [] S σ hD hR le_rfl v hv j
    rw [toFormula_sat]
    show (Formula.Always φ).sat σ v i ↔ (Formula.Always r.1).sat S v i
    simp only [Formula.Always, Formula.always, Formula.sat]
    rw [hτ]
    refine not_congr (exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ => ?_)
    exact not_congr (hsem j)

end Paper
