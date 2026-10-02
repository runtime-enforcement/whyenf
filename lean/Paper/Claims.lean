/-
  All results of the paper — theorems, lemmas and the claims made in the
  text — in the order of the paper, as statements.  The proofs are in
  `Paper/Proof/` (`theorem_4_3 : Theorem_4_3 Voc`, `claim_… : Claim_…`, …).
-/
import Paper.Compile
import Paper.TypeSystem

namespace Paper

variable {Voc : Vocabulary}

/-! ## §4.1 Let-normal form -/

/-- **Theorem 4.1** (l.1142–1145): for any formula `□φ` in MFOTL, there exists
    an equivalent `ψ` in let-normal form.  The lets of `ψ` bind fresh names:
    `ψ` is over `ℰ ⊎ L` for a finite set `L` of let names, and the
    equivalence is over the traces of the original signature
    (NOTES.md, N7).  As Figure 1, the equivalence is for valuations defined
    on the free variables (l.619). -/
def Theorem_4_1 (Voc : Vocabulary) : Prop :=
  ∀ φ : Formula Voc, φ.IsMFOTL →
    ∃ (L : Type) (_ : Finite L) (ιL : L → ℕ) (N : LNF (Voc.ext L ιL)),
      N.Valid ∧ N.FreshLets ∧
      ∀ σ v i, v.Covers φ.fv →
        ((Formula.Always φ).sat σ v i ↔ N.toFormula.sat (Str.embed σ) v i)

/-! ## §4.2 Guard extraction -/

/-- **Lemma 4.2** (l.1230–1233): if `Guards^m_X(Φ) = (π, φ)`, then every `κ ∈ π`
    binds every `x ∈ X`, and `⋁_{κ ∈ π} κ ∧ φ ≡ Φ`. -/
def Lemma_4_2 (Voc : Vocabulary) : Prop :=
  ∀ {m : Set Voc.ℰ} {X : Set Voc.𝕍} {Φ φ : Formula Voc} {π : GDisj Voc},
    Guards m X Φ = some (π, φ) → (∀ κ ∈ π, ∀ x ∈ X, κ.Binds x) ∧ Equiv (.and π.toFormula φ) Φ

/-- The equation behind `And⁺` (l.1184–1185):
    `π ∧ φⱼ ≡ π' ∧ φ'ⱼ ⟹ π ∧ ⋀ᵢ φᵢ ≡ π' ∧ ⋀_{i≠j} φᵢ ∧ φ'ⱼ`. -/
def Claim_andPos_equation (Voc : Vocabulary) : Prop :=
  ∀ (π π' φj φj' : Formula Voc) (others : List (Formula Voc))
    (h : Equiv (.and π φj) (.and π' φj')),
    Equiv (.and π (bigAnd (φj :: others))) (.and π' (.and (bigAnd others) φj'))

/-- The dual equation behind `And⁻` (l.1186–1188):
    `∀i. π → φᵢ ≡ π'ᵢ → φ'ᵢ ⟹ π → ⋀ᵢ φᵢ ≡ ⋁ᵢ π'ᵢ → ⋀ᵢ (π'ᵢ → φ'ᵢ)`. -/
def Claim_andNeg_equation (Voc : Vocabulary) : Prop :=
  ∀ (π : Formula Voc) (ps : List (Formula Voc × Formula Voc × Formula Voc))
    (h : ∀ p ∈ ps, Equiv (.imp π p.1) (.imp p.2.1 p.2.2)),
    Equiv (.imp π (bigAnd (ps.map Prod.fst)))
        (.imp (ps.foldr (fun p acc => Formula.or p.2.1 acc) .bot)
          (bigAnd (ps.map fun p => Formula.imp p.2.1 p.2.2)))

/-! ## §4.4 TypeLet (l.1444–1459) -/

/-- `TypeLet` on `φ_l S_[a,b] φ_r` (with `⧫ = ⊤ S`): `p` is guarded; "a `⧫` or `S`
    is causable only when its interval admits the present (`a = 0`) by causing
    the (right) operand; a `S` is suppressable when either `a > 0` and its left
    operand is suppressable or both its operands are" (l.1449–1452). -/
def Claim_typeLet_since (Voc : Vocabulary) : Prop :=
  ∀ {Ξ : RwSetting Voc} {T T' : Typed Voc} {p : Voc.ℰ} {xs : List Voc.𝕍}
    {ψ φl φr : Formula Voc} {I : Interval} (hχ : stripExists ψ = .since I φl φr)
    (h : TypeLet Ξ T p xs ψ = some T'),
    ∃ c s, T'.Γ p = some (true, c, s) ∧
        (c = true ↔ 0 ∈ I ∧ (RwAll Ξ T.Γ .C φr).Nonempty) ∧
        (s = true ↔ (RwAll Ξ T.Γ .S φl).Nonempty ∧ (0 ∈ I → (RwAll Ξ T.Γ .S φr).Nonempty))

/-- "A `●` or aggregation is neither causable or suppressable" (l.1453). -/
def Claim_typeLet_prev_agg (Voc : Vocabulary) : Prop :=
  ∀ {Ξ : RwSetting Voc} {T T' : Typed Voc} {p : Voc.ℰ} {xs : List Voc.𝕍}
    {ψ : Formula Voc} (hχ : (∃ I φ, stripExists ψ = .prev I φ) ∨
      ∃ ys ω ss gs φ, stripExists ψ = .agg ys ω ss gs φ)
    (h : TypeLet Ξ T p xs ψ = some T'),
    T'.Γ p = some (true, false, false)

/-- "Insufficient guarding is fatal for a temporal or aggregation let"
    (l.1454–1455). -/
def Claim_typeLet_fatal (Voc : Vocabulary) : Prop :=
  ∀ {Ξ : RwSetting Voc} {T : Typed Voc} {p : Voc.ℰ} {xs : List Voc.𝕍} {ψ : Formula Voc},
    let m : Set Voc.ℰ := Ξ.m T.Γ
    let X : Set Voc.𝕍 := {x | x ∈ xs} ∪ (stripExists ψ).fv
    ((∃ I φ, stripExists ψ = .since I .top φ ∧ Guards m φ.fv φ = none) ∨
     (∃ I φ, stripExists ψ = .prev I φ ∧ Guards m φ.fv φ = none) ∨
     (∃ ys ω ss gs φ, stripExists ψ = .agg ys ω ss gs φ ∧ Guards m φ.fv φ = none) ∨
     (∃ I φl φr, φl ≠ .top ∧ stripExists ψ = .since I φl φr ∧
        (Guards m X (.neg φl) = none ∨ Guards m X φr = none))) →
    TypeLet Ξ T p xs ψ = none

/-- "For a present let, it only downgrades `p` to filter-only" (l.1455–1457).
    By R13, this also holds for a body `∃ȳ. χ` where `χ` has a future
    operator. -/
def Claim_typeLet_present_unguarded (Voc : Vocabulary) : Prop :=
  ∀ {Ξ : RwSetting Voc} {T : Typed Voc} {p : Voc.ℰ}
    {xs : List Voc.𝕍} {ψ : Formula Voc}
    (hχ : ∀ I φl φr, stripExists ψ ≠ .since I φl φr)
    (hχ' : ∀ I φ, stripExists ψ ≠ .prev I φ) (hχ'' : ∀ ys ω ss gs φ, stripExists ψ ≠ .agg ys ω ss gs φ)
    (hg : Guards (Ξ.m T.Γ) ({x | x ∈ xs} ∪ (stripExists ψ).fv)
      (stripExists ψ) = none),
    ∃ T', TypeLet Ξ T p xs ψ = some T' ∧ T'.Γ p = some (false, false, false)

/-! ## §4.5 Dependency analysis -/

/-- The property stated in l.1559–1560, for the stable symbols *jointly*:
    applying stable functions repeatedly to finitely many values yields
    finitely many values. -/
def Claim_closure_finite (Voc : Vocabulary) : Prop :=
  ∀ (O : StabOrder Voc) {F : Set Voc.𝔽}, (∀ f ∈ F, Stable O f) →
    ∀ {V : Set Voc.𝔻}, V.Finite → {d | Closure F V d}.Finite

/-! ### Examples (l.1473–1565) -/

/-- "`C₁ = {(⊤,⊤) ⇒ A(0), (⊤,⊤) ⇒ ¬A(0)}` is unsatisfiable … This rules out `C₁`"
    (l.1473–1492). -/
def Claim_conflict_C1 (Voc : Vocabulary) : Prop :=
  ∀ (A : Voc.ℰ) (d : Voc.𝔻),
    ¬ ConflictCheck [] {⟨[[]], .top, .cau A [.const d]⟩, ⟨[[]], .top, .sup A [.const d]⟩}

/-- "… but allows `{(⊤, B(0)) ⇒ A(0), (⊤, ¬B(0)) ⇒ ¬A(0)}`" (l.1492–1494). -/
def Claim_conflict_C1' (Voc : Vocabulary) : Prop :=
  ∀ (A B : Voc.ℰ) (hAB : A ≠ B) (d : Voc.𝔻),
    ConflictCheck []
        {⟨[[]], .pred B [.const d], .cau A [.const d]⟩,
          ⟨[[]], .neg (.pred B [.const d]), .sup A [.const d]⟩}

/-- A vocabulary with `𝔻 = ℕ` and one unary function symbol `succ`. -/
abbrev VSucc : Vocabulary where
  𝔻 := ℕ
  ℰ := Unit
  finE := inferInstance
  ι := fun _ => 1
  𝕍 := Unit
  decV := inferInstance
  𝔽 := Unit
  ιF := fun _ => 1
  fhat := fun _ a => a 0 + 1
  Ω := Empty
  ι' := Empty.elim
  ωhat := fun ω => ω.elim

/-- "causing a fresh value on every iteration (e.g. `(A(x), ⊤) ⇒ A(x+1)`) is
    rejected" (l.1562–1564), whatever the global order. -/
def Claim_dfg_succ_rejected : Prop :=
  ∀ (O : StabOrder VSucc),
    ¬ DFGCheck O [] {(⟨[[.pred () [.var ()]]], .top, .cau () [.app () [.var ()]]⟩ : EClause VSucc)}

/-- "… while `(use(d), ⊤) ⇒ ¬use(d)` is accepted because no new domain values
    are generated by that clause" (l.1564–1565). -/
def Claim_dfg_use_accepted (Voc : Vocabulary) : Prop :=
  ∀ (O : StabOrder Voc) (use : Voc.ℰ) (d : Voc.𝕍),
    DFGCheck O [] {(⟨[[.pred use [.var d]]], .top, .sup use [.var d]⟩ : EClause Voc)}

/-! ## §4.6 Compilation -/

/-- **Theorem 4.3** (Compilation correctness, l.1646–1654): let
    `R ∈ Generate(□φ)` be a candidate clause set accepted by the two checks of
    §4.5, and assume that `P = Compile(ℒ, Γ, R, ≺)` is defined; then `P` is a
    sound enforcer for `□φ` with causable events `ℂ ∪ {Cau_p, Sup_p}`, on
    system traces without let-bound or obligation events.

    Spelled out:
    * `□φ` is a closed MFOTL formula and `LetNormalForm(□φ) = (ℒ, χ₁ … χ_n)` is
      a well-formed (`WF`; NOTES.md, N1, N6) valid let-normal form of it,
      equivalent on the traces without let events (NOTES.md, F6);
    * `Γ` is computed by Algorithm 3 (`TypeLets`), and `R` is one of the
      candidate clause sets of `Generate`;
    * `R` passes `ConflictCheck` and `DFGCheck` (for some global order `≼`);
    * `≺` is a topological order, `rs` enumerates `R`, and `Compile`
      succeeds;
    * `P` causes events of `ℂ` and the obligation events, and suppresses
      events of `𝕊`; the input traces contain no let or obligation events. -/
def Theorem_4_3 (Voc : Vocabulary) : Prop :=
  ∀ (Ξ : RwSetting Voc) (LetNormalForm : Formula Voc → LNF Voc) (φ : Formula Voc),
    φ.IsMFOTL → φ.fv = ∅ →
    let L := LetNormalForm (Formula.Always φ)
    L.Valid → WF Ξ φ L →
    (∀ σ : Trace Voc.toSignature, σ.length = ⊤ → Admissible {e | IsLet L.lets e} σ →
      ((Formula.Always φ).satTr σ Val.empty 0 ↔ L.toFormula.satTr σ Val.empty 0)) →
    ∀ T, TypeLets Ξ L.lets = some T →
    ∀ R, (∃ 𝒞, Rw Ξ T.Γ .C (bigAnd L.chis) 𝒞 ∧ ∃ C ∈ 𝒞, R ∈ Realizations Ξ T C) →
    ConflictCheck L.lets R → (∃ O, DFGCheck O L.lets R) →
    ∀ rk, TopoOrder L.lets R rk →
    ∀ rs : List (EClause Voc), (∀ c, c ∈ rs ↔ c ∈ R) →
    ∀ evTys colTy P, Compile Ξ L.lets T.Γ rs rk evTys colTy = some P →
      P.SoundEnforcer (Ξ.Cau ∪ Set.range Ξ.cauN ∪ Set.range Ξ.supN) Ξ.Sup
        (Admissible (NewNames Ξ L.lets)) (Formula.Always φ)

/-! ## Appendix A -/

/-- The binary rules `And^𝕊_L`, `And^𝕊_R` are instances of the n-ary `And^𝕊`
    of Figure 7. -/
def Figure7_AndS_binary (Voc : Vocabulary) : Prop :=
  ∀ (Ξ : RwSetting Voc) (Γ : ACtx Voc) (φ ψ : Formula Voc) (Δ : Set (EClause Voc)),
    (Typ Ξ Γ .S φ Δ → ψ.Present → Typ Ξ Γ .S (.and φ ψ) (ClauseSet.conj Δ ψ)) ∧
    (Typ Ξ Γ .S ψ Δ → φ.Present → Typ Ξ Γ .S (.and φ ψ) (ClauseSet.conj Δ φ))

/-- **Lemma A.1** (l.2142–2150).
    1. `m_Γ ⊢ (π, ψ) ⇝^p_x (π', ψ')` holds for some `(π', ψ')` iff every
       `κ ∈ π` binds `x` or `Γ ⊢ ψ : GRD(x)^p`; in particular, a guard for `x`
       can be extracted from a trigger iff the trigger guards `x`.
    2. `Guards^{m_Γ}_X(Φ) ≠ ⊥` iff `Γ ⊢ Φ : 𝔾⁺_X`. -/
def Lemma_A_1 (Voc : Vocabulary) : Prop :=
  (∀ (Ξ : RwSetting Voc) (Γ : ACtx Voc) (p : Pol) (x : Voc.𝕍) (π : GDisj Voc) (ψ : Formula Voc),
    (∃ π' ψ', TGX (Γ.m Ξ) p x π ψ π' ψ') ↔ (∀ κ ∈ π, κ.Binds x) ∨ Γ.Grd Ξ x p ψ) ∧
  (∀ (Ξ : RwSetting Voc) (Γ : ACtx Voc) (x : Voc.𝕍) (π : GDisj Voc) (ψ : Formula Voc),
    (∃ π' ψ', TGX (Γ.m Ξ) .pos x π ψ π' ψ') ↔ Γ.TrigGuards Ξ π ψ x) ∧
  (∀ (Ξ : RwSetting Voc) (Γ : ACtx Voc) (X : Set Voc.𝕍) (Φ : Formula Voc),
    Guards (Γ.m Ξ) X Φ ≠ none ↔ Γ.GSet Ξ .pos X Φ)

/-- **Theorem A.2** (l.2232–2237): `□φ`, with let-normal form `L`, is in
    EF-MFOTL with clause set `Δ` iff the compilation of §4 succeeds on `□φ`
    with candidate clause set `Δ`: `TypeLet` accepts all lets, and
    `Γ ⊢ χ ↪^ℂ 𝒞` for the resulting `Γ` and some `𝒞 ∋ Δ`.  The let-normal
    form is well formed (`LNF.WFA`; NOTES.md, N6). -/
def Theorem_A_2 (Voc : Vocabulary) : Prop :=
  ∀ (Ξ : RwSetting Voc) (L : LNF Voc), L.Valid → L.WFA → ∀ Δ : Set (EClause Voc),
    EFMFOTL Ξ L Δ ↔
      ∃ T, TypeLets Ξ L.lets = some T ∧ ∃ 𝒞, Rw Ξ T.Γ .C (bigAnd L.chis) 𝒞 ∧ Δ ∈ 𝒞

end Paper
