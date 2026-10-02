/-
  Where the values of guard variables come from.
-/
import Paper.Proof.Bound

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem evalList_get {v : Val Voc} : ∀ {ts : List (Term Voc)} {ds : List Voc.𝔻},
    Term.evalList v ts = some ds → ∀ {k : ℕ} {t : Term Voc}, ts[k]? = some t →
      ∃ d, ds[k]? = some d ∧ t.eval v = some d
  | [], ds, h, k, t, ht => by simp at ht
  | t₀ :: ts, ds, h, k, t, ht => by
    simp only [Term.evalList, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨d, hd, ds', hds', rfl⟩ := h
    rcases k with _ | k
    · simp at ht; subst ht; exact ⟨d, rfl, hd⟩
    · simp at ht; exact evalList_get hds' ht

/-- **Binding.** A variable bound by a satisfied guard takes its value from an
    atom of the guard or from an equation. -/
theorem bind_atom {S : Str Voc.toSignature} {j : ℕ} {κ : GConj Voc} {v : Val Voc}
    (hs : κ.toFormula.sat S v j) {x : Voc.𝕍} (hb : κ.Binds x) :
    (∃ (q : Voc.ℰ) (ts : List (Term Voc)) (k : ℕ), GAtom.pred q ts ∈ κ ∧ ts[k]? = some (Term.var x) ∧
      ∃ args ∈ RelOf S j q, ∃ a, args[k]? = some a ∧ v x = some a) ∨
    (∃ c, GAtom.eq x c ∈ κ ∧ v x = some c) := by
  obtain ⟨γ, hγ, ⟨q, ts, rfl, hx⟩ | ⟨c, rfl⟩⟩ := hb
  · have h := (sat_conj S v j κ).1 hs _ hγ
    simp only [GAtom.toFormula, Formula.sat] at h
    obtain ⟨ds, hds, ev, hev, he, ha⟩ := h
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
    obtain ⟨d, hd, hdx⟩ := evalList_get hds (List.getElem?_eq_some_iff.2 ⟨hk, hkx⟩)
    exact Or.inl ⟨q, ts, k, hγ, List.getElem?_eq_some_iff.2 ⟨hk, hkx⟩, ds, ⟨ev, hev, he, ha⟩, d, hd, hdx⟩
  · have h := (sat_conj S v j κ).1 hs _ hγ
    exact Or.inr ⟨c, hγ, h⟩

theorem GX.eqs {m : Set Voc.ℰ} {p X Φ π φ} (h : GX m p X Φ π φ) :
    ∀ κ ∈ π, ∀ x c, GAtom.eq x c ∈ κ → c ∈ Φ.eqConsts := by
  induction h with
  | none => intro κ hκ; simp at hκ; subst hκ; simp
  | vac => simp
  | pred => intro κ hκ x c h; simp at hκ; subst hκ; simp at h
  | eq X y c' _ => intro κ hκ x c h; simp at hκ; subst hκ; simp at h; simp [Formula.eqConsts, h.2]
  | andPos _ _ _ ih₁ ih₂ =>
    intro κ hκ x c hq
    simp only [GDisj.prod, List.mem_flatMap, List.mem_map] at hκ
    obtain ⟨κ₁, h₁, κ₂, h₂, rfl⟩ := hκ
    rcases List.mem_append.1 hq with hq | hq
    · exact Or.inl (ih₁ κ₁ h₁ x c hq)
    · exact Or.inr (ih₂ κ₂ h₂ x c hq)
  | andNeg _ _ ih₁ ih₂ =>
    intro κ hκ x c hq
    rcases List.mem_append.1 hκ with hκ | hκ
    · exact Or.inl (ih₁ κ hκ x c hq)
    · exact Or.inr (ih₂ κ hκ x c hq)
  | neg _ ih => exact ih

theorem atom_mem_disj {π : GDisj Voc} {κ : GConj Voc} (hκ : κ ∈ π) {q : Voc.ℰ} {ts : List (Term Voc)}
    (h : GAtom.pred q ts ∈ κ) : (q, ts) ∈ π.toFormula.atoms :=
  atoms_gdisj_sub π κ hκ _ h (by simp [GAtom.toFormula, Formula.atoms])

theorem eq_mem_disj {π : GDisj Voc} {κ : GConj Voc} (hκ : κ ∈ π) {x : Voc.𝕍} {c : Voc.𝔻}
    (h : GAtom.eq x c ∈ κ) : c ∈ π.toFormula.eqConsts := by
  induction π with
  | nil => simp at hκ
  | cons κ' π ih =>
    simp only [GDisj.toFormula, List.foldr_cons, Formula.or, Formula.eqConsts] at ih ⊢
    rcases List.mem_cons.1 hκ with rfl | hκ
    · left
      clear ih hκ
      induction κ with
      | nil => simp at h
      | cons γ κ ih' =>
        simp only [GConj.toFormula, List.foldr_cons, Formula.eqConsts]
        rcases List.mem_cons.1 h with rfl | h
        · left; simp [GAtom.toFormula, Formula.eqConsts]
        · right; exact ih' h
    · right; exact ih hκ

end Paper
