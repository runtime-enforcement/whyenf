/-
  Proofs of the claims of §4.2, §4.4 and §4.5 (`Paper/Claims.lean`).
-/
import Paper.Claims
import Paper.Proof.LetNormal
import Paper.Proof.Enforcer
import Paper.Proof.Dependency
import Paper.Proof.Compile

namespace Paper

variable {Voc : Vocabulary}

/-! ## §4.2 Guard extraction -/

section sec42
variable (σ : Str Voc.toSignature) (v : Val Voc) (i : ℕ)

theorem sat_bigAnd : ∀ φs : List (Formula Voc), (bigAnd φs).sat σ v i ↔ ∀ φ ∈ φs, φ.sat σ v i
  | [] => by simp [bigAnd, Formula.sat]
  | [φ] => by simp [bigAnd]
  | φ :: ψ :: φs => by
    rw [show bigAnd (φ :: ψ :: φs) = .and φ (bigAnd (ψ :: φs)) from rfl]
    simp only [Formula.sat, sat_bigAnd (ψ :: φs), List.mem_cons, forall_eq_or_imp]

end sec42

/-- The equation behind `And⁺` (l.1184–1185):
    `π ∧ φⱼ ≡ π' ∧ φ'ⱼ ⟹ π ∧ ⋀ᵢ φᵢ ≡ π' ∧ ⋀_{i≠j} φᵢ ∧ φ'ⱼ`. -/
theorem andPos_equation (π π' φj φj' : Formula Voc) (others : List (Formula Voc))
    (h : Equiv (.and π φj) (.and π' φj')) :
    Equiv (.and π (bigAnd (φj :: others))) (.and π' (.and (bigAnd others) φj')) := by
  intro σ v i
  have e := h σ v i
  simp only [Formula.sat, sat_bigAnd, List.mem_cons, forall_eq_or_imp] at e ⊢
  constructor
  · rintro ⟨hπ, hj, ho⟩; exact ⟨(e.1 ⟨hπ, hj⟩).1, ho, (e.1 ⟨hπ, hj⟩).2⟩
  · rintro ⟨hπ', ho, hj'⟩; exact ⟨(e.2 ⟨hπ', hj'⟩).1, (e.2 ⟨hπ', hj'⟩).2, ho⟩

/-- The dual equation behind `And⁻` (l.1186–1188):
    `∀i. π → φᵢ ≡ π'ᵢ → φ'ᵢ ⟹ π → ⋀ᵢ φᵢ ≡ ⋁ᵢ π'ᵢ → ⋀ᵢ (π'ᵢ → φ'ᵢ)`. -/
theorem andNeg_equation (π : Formula Voc) (ps : List (Formula Voc × Formula Voc × Formula Voc))
    (h : ∀ p ∈ ps, Equiv (.imp π p.1) (.imp p.2.1 p.2.2)) :
    Equiv (.imp π (bigAnd (ps.map Prod.fst)))
      (.imp (ps.foldr (fun p acc => Formula.or p.2.1 acc) .bot)
        (bigAnd (ps.map fun p => Formula.imp p.2.1 p.2.2))) := by
  intro σ v i
  have hor : ∀ qs : List (Formula Voc × Formula Voc × Formula Voc),
      (qs.foldr (fun p acc => Formula.or p.2.1 acc) .bot).sat σ v i ↔ ∃ p ∈ qs, p.2.1.sat σ v i := by
    intro qs; induction qs with
    | nil => simp
    | cons q qs ih => simp [ih]
  simp only [sat_imp, sat_bigAnd, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, hor]
  have e : ∀ p ∈ ps, ((π.sat σ v i → p.1.sat σ v i) ↔ (p.2.1.sat σ v i → p.2.2.sat σ v i)) := by
    intro p hp; have := h p hp σ v i; simpa only [sat_imp] using this
  constructor
  · intro H _ _ _ a ha
    exact (e a ha).1 fun hπ => H hπ a ha
  · intro H hπ a ha
    by_cases hq : a.2.1.sat σ v i
    · exact (e a ha).2 (fun hq' => H a ha hq' a ha hq') hπ
    · exact (e a ha).2 (fun h' => absurd h' hq) hπ

/-- The free variables of a guard atom, conjunction and disjunction. -/
theorem fv_gatom (γ : GAtom Voc) : γ.toFormula.fv = match γ with
    | .pred _ ts => Term.varsList ts
    | .eq x _ => {x} := by
  cases γ <;> rfl

theorem fv_gconj (κ : GConj Voc) : κ.toFormula.fv = {x | ∃ γ ∈ κ, x ∈ γ.toFormula.fv} := by
  induction κ with
  | nil => simp [GConj.toFormula, Formula.fv]
  | cons γ κ ih =>
    simp only [GConj.toFormula, List.foldr_cons, Formula.fv] at ih ⊢
    rw [ih]; ext x; simp

theorem fv_gdisj (π : GDisj Voc) : π.toFormula.fv = {x | ∃ κ ∈ π, x ∈ κ.toFormula.fv} := by
  induction π with
  | nil => simp [GDisj.toFormula, Formula.bot, Formula.fv]
  | cons κ π ih =>
    simp only [GDisj.toFormula, List.foldr_cons, Formula.or, Formula.fv] at ih ⊢
    rw [ih]; ext x; simp

theorem mem_varsList_of_mem {x : Voc.𝕍} {ts : List (Term Voc)} (h : Term.var x ∈ ts) :
    x ∈ Term.varsList ts := by
  induction ts with
  | nil => simp at h
  | cons t ts ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp [Term.varsList, Term.vars]
    · exact Or.inr (ih h)

/-- The atoms of the guards come from `Φ`: `fv(π) ⊆ fv(Φ)`. -/
theorem GX.fv_sub {m : Set Voc.ℰ} {p X Φ π φ} (h : GX m p X Φ π φ) :
    ∀ κ ∈ π, κ.toFormula.fv ⊆ Φ.fv := by
  induction h with
  | none => intro κ hκ; simp at hκ; subst hκ; simp [GConj.toFormula, Formula.fv]
  | vac => simp
  | pred X p ts =>
    intro κ hκ; simp at hκ; subst hκ
    simp [GConj.toFormula, GAtom.toFormula, Formula.fv]
  | eq X x c =>
    intro κ hκ; simp at hκ; subst hκ
    simp [GConj.toFormula, GAtom.toFormula, Formula.fv]
  | andPos _ _ _ ih₁ ih₂ =>
    intro κ hκ
    simp only [GDisj.prod, List.mem_flatMap, List.mem_map] at hκ
    obtain ⟨κ₁, h₁, κ₂, h₂, rfl⟩ := hκ
    rw [fv_gconj]
    rintro x ⟨γ, hγ, hx⟩
    rcases List.mem_append.1 hγ with hγ | hγ
    · exact Or.inl (ih₁ κ₁ h₁ (by rw [fv_gconj]; exact ⟨γ, hγ, hx⟩))
    · exact Or.inr (ih₂ κ₂ h₂ (by rw [fv_gconj]; exact ⟨γ, hγ, hx⟩))
  | andNeg _ _ ih₁ ih₂ =>
    intro κ hκ
    rcases List.mem_append.1 hκ with h | h
    · exact (ih₁ κ h).trans Set.subset_union_left
    · exact (ih₂ κ h).trans Set.subset_union_right
  | neg _ ih => exact ih

theorem Binds.mem_fv {κ : GConj Voc} {x : Voc.𝕍} (h : κ.Binds x) : x ∈ κ.toFormula.fv := by
  rw [fv_gconj]
  obtain ⟨γ, hγ, ⟨p, ts, rfl, hx⟩ | ⟨c, rfl⟩⟩ := h
  · exact ⟨_, hγ, mem_varsList_of_mem hx⟩
  · exact ⟨_, hγ, rfl⟩

end Paper

/-! ## §4.4 TypeLet (l.1444–1459) -/

namespace Paper

variable {Voc : Vocabulary}

theorem CSet.map_nonempty {𝒞 : CSet Voc} {f} : (𝒞.map f).Nonempty ↔ 𝒞.Nonempty := by
  constructor
  · rintro ⟨_, C, hC, -⟩; exact ⟨C, hC⟩
  · rintro ⟨C, hC⟩; exact ⟨_, C, hC, rfl⟩

theorem CSet.tensor_nonempty {𝒞₁ 𝒞₂ : CSet Voc} :
    (𝒞₁.tensor 𝒞₂).Nonempty ↔ 𝒞₁.Nonempty ∧ 𝒞₂.Nonempty := by
  constructor
  · rintro ⟨_, C₁, h₁, C₂, h₂, -⟩; exact ⟨⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩
  · rintro ⟨⟨C₁, h₁⟩, ⟨C₂, h₂⟩⟩; exact ⟨_, C₁, h₁, C₂, h₂, rfl⟩

theorem gate_nonempty {q : Voc.ℰ} {xs : List Voc.𝕍} {𝒞 : CSet Voc} :
    (gate q xs 𝒞).Nonempty ↔ 𝒞.Nonempty := CSet.map_nonempty

/-- `⊤` cannot be suppressed. -/
theorem RwAll_S_top (Ξ : RwSetting Voc) (Γ : LetCtx Voc) : RwAll Ξ Γ .S .top = ∅ := by
  ext C
  simp only [RwAll, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  intro 𝒞 h
  generalize hα : Mode.S = α at h
  generalize hφ : (Formula.top : Formula Voc) = φ at h
  cases h with
  | top => cases hα
  | andS φs j hl =>
    exfalso
    match φs, hl with
    | _ :: _ :: _, _ => simp [bigAnd] at hφ
  | andC φs _ hl =>
    exfalso
    match φs, hl with
    | _ :: _ :: _, _ => simp [bigAnd] at hφ
  | futNextN n _ hn =>
    exfalso
    cases n with
    | zero => omega
    | succ n =>
      rw [nextN, Function.iterate_succ_apply'] at hφ
      cases hφ
  | _ => simp_all

theorem ne_empty_iff_nonempty' {α : Type} (s : Set α) : (s ≠ ∅) ↔ s.Nonempty :=
  Set.nonempty_iff_ne_empty.symm

/-- `TypeLet` on `φ_l S_[a,b] φ_r` (with `⧫ = ⊤ S`): `p` is guarded; "a `⧫` or `S`
    is causable only when its interval admits the present (`a = 0`) by causing
    the (right) operand; a `S` is suppressable when either `a > 0` and its left
    operand is suppressable or both its operands are" (l.1449–1452). -/
theorem typeLet_since {Ξ : RwSetting Voc} {T T' : Typed Voc} {p : Voc.ℰ} {xs : List Voc.𝕍}
    {ψ φl φr : Formula Voc} {I : Interval} (hχ : stripExists ψ = .since I φl φr)
    (h : TypeLet Ξ T p xs ψ = some T') :
    ∃ c s, T'.Γ p = some (true, c, s) ∧
      (c = true ↔ 0 ∈ I ∧ (RwAll Ξ T.Γ .C φr).Nonempty) ∧
      (s = true ↔ (RwAll Ξ T.Γ .S φl).Nonempty ∧ (0 ∈ I → (RwAll Ξ T.Γ .S φr).Nonempty)) := by
  unfold TypeLet at h
  simp only [hχ] at h
  cases φl with
  | top =>
    simp only at h
    split_ifs at h with hg hI <;> cases h <;> simp only [Function.update_self] <;> refine ⟨_, _, rfl, ?_, ?_⟩ <;>
      simp only [decide_eq_true_eq, ne_empty_iff_nonempty', gate_nonempty, RwAll_S_top,
        Set.not_nonempty_empty, false_and] <;> simp [hI]
  | _ =>
    simp only at h
    split_ifs at h with hg hI <;> cases h <;> simp only [Function.update_self] <;> refine ⟨_, _, rfl, ?_, ?_⟩ <;>
      simp only [decide_eq_true_eq, ne_empty_iff_nonempty', gate_nonempty,
        CSet.tensor_nonempty, Set.not_nonempty_empty] <;> simp [hI]

/-- "A `●` or aggregation is neither causable or suppressable" (l.1453). -/
theorem typeLet_prev_agg {Ξ : RwSetting Voc} {T T' : Typed Voc} {p : Voc.ℰ} {xs : List Voc.𝕍}
    {ψ : Formula Voc} (hχ : (∃ I φ, stripExists ψ = .prev I φ) ∨
      ∃ ys ω ss gs φ, stripExists ψ = .agg ys ω ss gs φ)
    (h : TypeLet Ξ T p xs ψ = some T') : T'.Γ p = some (true, false, false) := by
  unfold TypeLet at h
  rcases hχ with ⟨I, φ, hχ⟩ | ⟨ys, ω, ss, gs, φ, hχ⟩ <;> simp only [hχ] at h <;>
    split_ifs at h <;> cases h <;> simp

/-- "Insufficient guarding is fatal for a temporal or aggregation let"
    (l.1454–1455). -/
theorem typeLet_fatal {Ξ : RwSetting Voc} {T : Typed Voc} {p : Voc.ℰ} {xs : List Voc.𝕍}
    {ψ : Formula Voc} :
    let m : Set Voc.ℰ := Ξ.m T.Γ
    let X : Set Voc.𝕍 := {x | x ∈ xs} ∪ (stripExists ψ).fv
    ((∃ I φ, stripExists ψ = .since I .top φ ∧ Guards m φ.fv φ = none) ∨
     (∃ I φ, stripExists ψ = .prev I φ ∧ Guards m φ.fv φ = none) ∨
     (∃ ys ω ss gs φ, stripExists ψ = .agg ys ω ss gs φ ∧ Guards m φ.fv φ = none) ∨
     (∃ I φl φr, φl ≠ .top ∧ stripExists ψ = .since I φl φr ∧
        (Guards m X (.neg φl) = none ∨ Guards m X φr = none))) →
    TypeLet Ξ T p xs ψ = none := by
  intro m X h
  unfold TypeLet
  rcases h with ⟨I, φ, hχ, hg⟩ | ⟨I, φ, hχ, hg⟩ | ⟨ys, ω, ss, gs, φ, hχ, hg⟩ |
      ⟨I, φl, φr, hl, hχ, hg⟩
  · simp only [hχ, m] at hg ⊢; simp only [hg, ↓reduceIte]
  · simp only [hχ, m] at hg ⊢; simp only [hg, ↓reduceIte]
  · simp only [hχ, m] at hg ⊢; simp only [hg, ↓reduceIte]
  · simp only [X, hχ, m] at hg ⊢
    cases φl with
    | top => exact absurd rfl hl
    | _ => simp only [hg, ↓reduceIte]

/-- "For a present let, it only downgrades `p` to filter-only" (l.1455–1457).
    By R13, this also holds for a body `∃ȳ. χ` where `χ` has a future
    operator. -/
theorem typeLet_present_unguarded {Ξ : RwSetting Voc} {T : Typed Voc} {p : Voc.ℰ}
    {xs : List Voc.𝕍} {ψ : Formula Voc}
    (hχ : ∀ I φl φr, stripExists ψ ≠ .since I φl φr)
    (hχ' : ∀ I φ, stripExists ψ ≠ .prev I φ) (hχ'' : ∀ ys ω ss gs φ, stripExists ψ ≠ .agg ys ω ss gs φ)
    (hg : Guards (Ξ.m T.Γ) ({x | x ∈ xs} ∪ (stripExists ψ).fv)
      (stripExists ψ) = none) :
    ∃ T', TypeLet Ξ T p xs ψ = some T' ∧ T'.Γ p = some (false, false, false) := by
  unfold TypeLet
  generalize hs : stripExists ψ = χ at hχ hχ' hχ'' hg
  cases χ with
  | since I φl φr => exact absurd rfl (hχ I φl φr)
  | prev I φ => exact absurd rfl (hχ' I φ)
  | agg ys ω ss gs φ => exact absurd rfl (hχ'' ys ω ss gs φ)
  | _ => simp_all

end Paper

/-! ## §4.5 Examples (l.1473–1565) -/

namespace Paper

variable {Voc : Vocabulary}

theorem sat_trig_top (σ : Str Voc.toSignature) (v : Val Voc) (i : ℕ) (ε : Effect Voc) :
    (EClause.trig ⟨[[]], .top, ε⟩).sat σ v i := by
  simp [EClause.trig, Formula.sat, sat_disj, sat_conj]

/-- "`C₁ = {(⊤,⊤) ⇒ A(0), (⊤,⊤) ⇒ ¬A(0)}` is unsatisfiable … This rules out `C₁`"
    (l.1473–1492). -/
theorem conflict_C1 (A : Voc.ℰ) (d : Voc.𝔻) :
    ¬ ConflictCheck [] {⟨[[]], .top, .cau A [.const d]⟩, ⟨[[]], .top, .sup A [.const d]⟩} := by
  intro h
  refine h ⟨[[]], .top, .cau A [.const d]⟩ (by simp) ⟨[[]], .top, .sup A [.const d]⟩ (by simp)
    rfl rfl rfl ?_
  let σ : Str Voc.toSignature := ⟨fun _ => 0, fun _ => ∅⟩
  refine ⟨σ, σ, 0, 0, fun _ => some d, fun _ => some d, ?_, ?_, ?_, ?_, ?_, [d], ?_, ?_⟩
  · simp [Effect.deferred, Str.AgreeOn]
  · intro x _; rfl
  · intro x _; rfl
  · exact sat_trig_top _ _ _ _
  · exact sat_trig_top _ _ _ _
  · simp [Effect.args, Term.evalList, Term.eval]
  · simp [Effect.args, Term.evalList, Term.eval]

/-- "… but allows `{(⊤, B(0)) ⇒ A(0), (⊤, ¬B(0)) ⇒ ¬A(0)}`" (l.1492–1494). -/
theorem conflict_C1' (A B : Voc.ℰ) (hAB : A ≠ B) (d : Voc.𝔻) :
    ConflictCheck []
      {⟨[[]], .pred B [.const d], .cau A [.const d]⟩,
        ⟨[[]], .neg (.pred B [.const d]), .sup A [.const d]⟩} := by
  set c₁ : EClause Voc := ⟨[[]], .pred B [.const d], .cau A [.const d]⟩
  set c₂ : EClause Voc := ⟨[[]], .neg (.pred B [.const d]), .sup A [.const d]⟩
  set R : Set (EClause Voc) := {c₁, c₂}
  have hdec : ∀ q e : Voc.ℰ, Decomp ([] : List (LetDef Voc)) q e → q = e := by
    intro q e h; cases h with
    | base => rfl
    | let_ hd => simp at hd
  have hpreds : ∀ c ∈ R, c.trigPreds = {B} := by
    intro c hc
    rcases hc with rfl | rfl <;> ext e <;>
      simp [c₁, c₂, EClause.trigPreds, EClause.trigAtoms, Formula.atoms]
  have hedge : ∀ e e', EDG [] R e e' → e = B ∧ e' = A := by
    rintro e e' ⟨c, a, hc, ⟨q, hq, hd⟩, hn, -, -⟩
    rw [hpreds c hc] at hq
    refine ⟨(hdec _ _ hd) ▸ hq, ?_⟩
    rw [← hn]; rcases hc with rfl | rfl <;> rfl
  have hreach : ∀ x y, Reach [] R x y → x = y ∨ (x = B ∧ y = A) := by
    intro x y h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ he ih =>
      obtain ⟨rfl, rfl⟩ := hedge _ _ he
      rcases ih with rfl | ⟨rfl, h⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd h.symm hAB
  have hBA : SCCBefore [] R B A := by
    refine ⟨Relation.ReflTransGen.single ⟨c₁, .C, by simp [R], ⟨B, by simp [hpreds c₁ (by simp [R])],
      Decomp.base (by simp [IsLet])⟩, rfl, by simp [IsLet], rfl⟩, fun h => ?_⟩
    rcases hreach _ _ h with h | ⟨h, -⟩ <;> exact hAB h
  intro x hx y hy hxC hyS _
  have hx' : x = c₁ := by
    rcases hx with rfl | rfl
    · rfl
    · simp [c₂, Effect.pol] at hxC
  have hy' : y = c₂ := by
    rcases hy with rfl | rfl
    · simp [c₁, Effect.pol] at hyS
    · rfl
  subst hx' hy'
  rintro ⟨σ₁, σ₂, i₁, i₂, v₁, v₂, hag, -, -, h₁, h₂, -⟩
  simp only [c₁, Effect.deferred, Bool.false_eq_true, ↓reduceIte] at hag
  obtain ⟨⟨-, hD⟩, rfl⟩ := hag
  simp only [withLets, List.foldr_nil, EClause.trig, Formula.sat, c₁, c₂] at h₁ h₂
  obtain ⟨-, ds, hds, ev, hev, he, ha⟩ := h₁
  apply h₂.2
  refine ⟨ds, ?_, ev, (hD i₁ ev (he ▸ hBA)).1 hev, he, ha⟩
  simpa [Term.evalList, Term.eval] using hds

/-- "causing a fresh value on every iteration (e.g. `(A(x), ⊤) ⇒ A(x+1)`) is
    rejected" (l.1562–1564), whatever the global order. -/
theorem dfg_succ_rejected (O : StabOrder VSucc) :
    ¬ DFGCheck O [] {(⟨[[.pred () [.var ()]]], .top, .cau () [.app () [.var ()]]⟩ : EClause VSucc)} := by
  rintro ⟨h, -⟩
  refine h _ (.app () [.var ()]) ((), 0) ((), 0) ⟨rfl, (), ⟨[.var ()], ?_, rfl⟩, rfl, rfl, ?_⟩ ?_
    Relation.ReflTransGen.refl
  · left; exact ⟨[.pred () [.var ()]], by simp, by simp⟩
  · simp [Term.vars, Term.varsList]
  · rintro ⟨-, -, hst⟩
    have hs : ∀ n : ℕ, O.le (n + 1) n := by
      intro n
      obtain ⟨k, hk⟩ := hst () (by simp [Term.funs]) (fun _ => n)
      exact hk
    have hdown : ∀ n : ℕ, O.le (n + 1) 0 := by
      intro n; induction n with
      | zero => exact hs 0
      | succ n ih => exact O.trans _ _ _ (hs (n + 1)) ih
    exact Set.infinite_of_injective_forall_mem (f := fun n : ℕ => n + 1)
      (fun a b h => by simpa using h) hdown (O.finDown 0)

/-- "… while `(use(d), ⊤) ⇒ ¬use(d)` is accepted because no new domain values
    are generated by that clause" (l.1564–1565). -/
theorem dfg_use_accepted (O : StabOrder Voc) (use : Voc.ℰ) (d : Voc.𝕍) :
    DFGCheck O [] {(⟨[[.pred use [.var d]]], .top, .sup use [.var d]⟩ : EClause Voc)} := by
  refine ⟨?_, ?_⟩
  · intro c t q q' he hns
    exfalso; apply hns
    obtain ⟨hc, x, -, -, ht, -⟩ := he
    rw [Set.mem_singleton_iff] at hc; subst hc
    have : t = .var d := by
      rcases q' with ⟨_, _ | _ | j⟩ <;> simp [Effect.args] at ht; exact ht.symm
    subst this
    exact ⟨by simp [AggResult], by simp [AggResult], by simp [Term.funs]⟩
  · rintro q q' ⟨_, hd, -⟩; simp at hd

/-! ## The claims -/

theorem claim_andPos_equation : Claim_andPos_equation Voc := @andPos_equation Voc
theorem claim_andNeg_equation : Claim_andNeg_equation Voc := @andNeg_equation Voc
theorem claim_typeLet_since : Claim_typeLet_since Voc := @typeLet_since Voc
theorem claim_typeLet_prev_agg : Claim_typeLet_prev_agg Voc := @typeLet_prev_agg Voc
theorem claim_typeLet_fatal : Claim_typeLet_fatal Voc := @typeLet_fatal Voc
theorem claim_typeLet_present_unguarded : Claim_typeLet_present_unguarded Voc := @typeLet_present_unguarded Voc
theorem claim_conflict_C1 : Claim_conflict_C1 Voc := @conflict_C1 Voc
theorem claim_conflict_C1' : Claim_conflict_C1' Voc := @conflict_C1' Voc
theorem claim_dfg_succ_rejected : Claim_dfg_succ_rejected := @dfg_succ_rejected
theorem claim_dfg_use_accepted : Claim_dfg_use_accepted Voc := @dfg_use_accepted Voc

end Paper
