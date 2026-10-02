/-
  §2.3 Enforcers (main.tex l.631–677, Algorithm 1).
-/
import Paper.MFOTL

namespace Paper

variable {Sig : Signature}

/-- A proactive enforcer `ℰ = (𝒮, s₀, μ, ν)` (l.644–651) for the fixed sets
    `ℂ ⊆ ℰ` of causable and `𝕊 ⊆ ℰ` of suppressable event names:
    `μ : 𝒮 × 𝒯 × ℕ × 𝔻𝔹 → 𝒮 × 𝔻𝔹_ℂ × 𝔻𝔹_𝕊` and
    `ν : 𝒮 × 𝒯 × ℕ → 𝒮 × (𝔻𝔹_ℂ ∪ {⊥})` (`⊥` is `none`). -/
structure Enforcer (Sig : Signature) (Cau Sup : Set Sig.ℰ) where
  𝒮 : Type
  s₀ : 𝒮
  μ : 𝒮 → Trace Sig → ℕ → DB Sig → 𝒮 × DBOf Sig Cau × DBOf Sig Sup
  ν : 𝒮 → Trace Sig → ℕ → 𝒮 × Option (DBOf Sig Cau)

namespace Enforcer

variable {Cau Sup : Set Sig.ℰ} (E : Enforcer Sig Cau Sup)

/-! ## Algorithm 1

`σ · (τ, D)` is partial (`Trace.snoc?`): the result is a trace only if the
appended database is finite (NOTES.md, N4).  The algorithm is therefore a
partial function (`Option`). -/

/-- Line 4: `for t ∈ {τ_i, …, τ_{i+1} − 1}: (s, C') ← ν(s, σ, t);
    if C' ≠ ⊥ then σ ← σ · (t, C')`. -/
noncomputable def proLoop : List ℕ → E.𝒮 × Trace Sig → Option (E.𝒮 × Trace Sig)
  | [], st => some st
  | t :: ts, (s, σ) =>
    match E.ν s σ t with
    | (s', none) => proLoop ts (s', σ)
    | (s', some C') => (σ.snoc? t C'.1).bind fun σ' => proLoop ts (s', σ')

/-- `{τ_i, …, τ_{i+1} − 1}` in increasing order; empty if `i = |ρ| − 1`. -/
def proRange (ρ : Trace Sig) (i : ℕ) : List ℕ :=
  if ((i + 1 : ℕ) : ℕ∞) < ρ.length then List.range' (ρ.τ i) (ρ.τ (i + 1) - ρ.τ i) else []

/-- One iteration `i ∈ {0, …, |ρ| − 1}` of the outer loop of Algorithm 1:
    `(s, C, S) ← μ(s, σ, τᵢ, Dᵢ); σ ← σ · (τᵢ, (Dᵢ ∖ S) ∪ C)`, then line 4. -/
noncomputable def iter (ρ : Trace Sig) (i : ℕ) : E.𝒮 × Trace Sig → Option (E.𝒮 × Trace Sig)
  | (s, σ) =>
    match E.μ s σ (ρ.τ i) (ρ.D i) with
    | (s', C, S) => (σ.snoc? (ρ.τ i) ((ρ.D i \ S.1) ∪ C.1)).bind fun σ' =>
        E.proLoop (proRange ρ i) (s', σ')

/-- The state of Algorithm 1 after the first `k` iterations of the outer loop,
    starting from `s ← s₀; σ ← ε`. -/
noncomputable def run (ρ : Trace Sig) : ℕ → Option (E.𝒮 × Trace Sig)
  | 0 => some (E.s₀, Trace.empty)
  | k + 1 => (run ρ k).bind (E.iter ρ k)

/-! ### The output trace `ℰ(ρ)` -/

/-- For an infinite input, the outer loop does not terminate; the output trace
    is the limit of the traces `σ` built by the loop (NOTES.md, N4).  Its
    `j`-th element is the `j`-th element of `σ` after `j + 1` iterations,
    which has at least `j + 1` elements. -/
noncomputable def limitElem (ρ : Trace Sig) (hall : ∀ k, (E.run ρ k).isSome) (j : ℕ) :
    ℕ × DB Sig :=
  ((E.run ρ (j + 1)).get (hall _)).2.seq.get? j |>.getD (0, ∅)


/-- `ℰ(ρ)`: the output trace of Algorithm 1 (the `σ` of `return σ`).
    `none` if some `σ · (τ, D)` of the run is undefined.  For an
    infinite input, it is the infinite trace whose `j`-th element is
    `limitElem j` (NOTES.md, N4); such a trace always exists
    (`Enforcer.limit`, `Paper/Proof/Enforcer.lean`). -/
noncomputable def out (ρ : Trace Sig) : Option (Trace Sig) :=
  match ρ.seq with
  | .fin l => (E.run ρ l.length).map Prod.snd
  | .inf _ =>
    open Classical in
    if hall : ∀ k, (E.run ρ k).isSome then
      if h : ∃ σ : Trace Sig, σ.seq = .inf (E.limitElem ρ hall) then some h.choose else none
    else none

/-- **Soundness** (l.674–677): `ℰ` is sound w.r.t. a closed `φ` if for any
    system trace `σ ∈ 𝒯`, `∅, 0 ⊨_{ℰ(σ)} φ`.  Figure 1 gives a semantics on
    infinite traces only, so `σ` ranges over the infinite traces, and
    `ℰ(σ)` must be defined (NOTES.md, N4). -/
def Sound {Voc : Vocabulary} {Cau Sup : Set Voc.ℰ} (φ : Formula Voc) (E : Enforcer Voc.toSignature Cau Sup) : Prop :=
  φ.fv = ∅ → ∀ σ : Trace Voc.toSignature, σ.length = ⊤ →
    ∃ σ', E.out σ = some σ' ∧ φ.satTr σ' Val.empty 0

end Enforcer

end Paper
