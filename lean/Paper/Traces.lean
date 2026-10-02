/-
  §2.1 Traces (main.tex l.469–511).

  Every definition carries the paper line it transcribes.  Formalization
  choices and the remaining differences with the paper are listed in
  `NOTES.md`.
-/
import Mathlib

namespace Paper

/-- A signature `Σ = (𝔻, ℰ, ι)` (l.471–473): a domain `𝔻`, a *finite* set of
    event names `ℰ`, and an arity function `ι : ℰ → ℕ`. -/
structure Signature where
  𝔻 : Type
  ℰ : Type
  [finE : Finite ℰ]
  ι : ℰ → ℕ

variable (Sig : Signature)

/-- An event `(e, d̄) ∈ ℰ × 𝔻^{ι(e)}` (l.472). -/
@[ext] structure Event where
  e : Sig.ℰ
  args : List Sig.𝔻
  arity : args.length = Sig.ι e

/-- `𝔻𝔹 ≔ 𝒫({(e, d̄) ∣ e ∈ ℰ, d̄ ∈ 𝔻^{ι(e)}})` (l.474). -/
abbrev DB := Set (Event Sig)

/-- `𝔻𝔹_E ≔ {D ∈ 𝔻𝔹 ∣ ∀ (e, d̄) ∈ D. e ∈ E}` (l.475). -/
def DBOf (E : Set Sig.ℰ) : Set (DB Sig) := {D | ∀ ev ∈ D, ev.e ∈ E}

/-- Finite or infinite sequences (l.493: `k ∈ ℕ ∪ {∞}`). -/
inductive Seq (α : Type) where
  | fin : List α → Seq α
  | inf : (ℕ → α) → Seq α

namespace Seq
variable {α : Type}

/-- `|σ|`. -/
def length : Seq α → ℕ∞
  | fin l => l.length
  | inf _ => ⊤

/-- The `i`-th element, if `i < |σ|`. -/
def get? : Seq α → ℕ → Option α
  | fin l, i => l[i]?
  | inf s, i => some (s i)

end Seq

/-- A trace (l.492–495): a sequence `(τᵢ, Dᵢ)` of timestamps `τᵢ ∈ ℕ` and *finite*
    databases `Dᵢ ∈ 𝔻𝔹`, whose timestamps grow monotonically and progress if
    the trace is infinite: `τᵢ ≤ τᵢ₊₁` for all `i` with `i + 1 < |σ|`. -/
structure Trace where
  seq : Seq (ℕ × DB Sig)
  finite : ∀ i p, seq.get? i = some p → p.2.Finite
  mono : ∀ i p q, seq.get? i = some p → seq.get? (i + 1) = some q → p.1 ≤ q.1
  progress : seq.length = ⊤ → ∀ τ : ℕ, ∃ i p, seq.get? i = some p ∧ τ < p.1

variable {Sig}

namespace Trace

/-- `|σ|`. -/
def length (σ : Trace Sig) : ℕ∞ := σ.seq.length

/-- `τᵢ` (junk `0` if `i ≥ |σ|`). -/
def τ (σ : Trace Sig) (i : ℕ) : ℕ := ((σ.seq.get? i).map Prod.fst).getD 0

/-- `Dᵢ` (junk `∅` if `i ≥ |σ|`). -/
def D (σ : Trace Sig) (i : ℕ) : DB Sig := ((σ.seq.get? i).map Prod.snd).getD ∅

/-- The empty trace `ε` (l.497). -/
def empty : Trace Sig where
  seq := .fin []
  finite := by simp [Seq.get?]
  mono := by simp [Seq.get?]
  progress := by simp [Seq.length]

/-- The last timestamp of a finite, non-empty trace. -/
def lastTs? (σ : Trace Sig) : Option ℕ :=
  match σ.seq with
  | .fin l => l.getLast?.map Prod.fst
  | .inf _ => none

/-- Can `(τ, D)` be appended to `σ` such that the result is again a trace?
    (`σ` finite, `D` finite, `τ` not smaller than the last timestamp.) -/
def CanSnoc (σ : Trace Sig) (τ : ℕ) (D : DB Sig) : Prop :=
  (∃ l, σ.seq = .fin l) ∧ D.Finite ∧ ∀ τ' ∈ σ.lastTs?, τ' ≤ τ

/-- `σ · (τ, D)`: append one element to a finite trace (Algorithm 1, l.662/664). -/
noncomputable def snoc (σ : Trace Sig) (τ : ℕ) (D : DB Sig) (h : σ.CanSnoc τ D) : Trace Sig :=
  have hs := Classical.choose_spec h.1
  have hτ : ∀ τ' ∈ (Classical.choose h.1).getLast?.map Prod.fst, τ' ≤ τ := by
    intro τ' h'; exact h.2.2 τ' (by unfold lastTs?; rw [hs]; exact h')
  have hok : ∀ (l : List (ℕ × DB Sig)), (∀ i p, (Seq.fin l).get? i = some p → p.2.Finite) →
      (∀ i p q, (Seq.fin l).get? i = some p → (Seq.fin l).get? (i + 1) = some q → p.1 ≤ q.1) →
      (∀ τ' ∈ l.getLast?.map Prod.fst, τ' ≤ τ) →
      (∀ i p, (Seq.fin (l ++ [(τ, D)])).get? i = some p → p.2.Finite) ∧
      (∀ i p q, (Seq.fin (l ++ [(τ, D)])).get? i = some p →
        (Seq.fin (l ++ [(τ, D)])).get? (i + 1) = some q → p.1 ≤ q.1) := by
    intro l hfin hmono hτ
    have hD := h.2.1
    simp only [Seq.get?] at *
    have key : ∀ i p, (l ++ [(τ, D)])[i]? = some p →
        (i < l.length ∧ l[i]? = some p) ∨ (i = l.length ∧ p = (τ, D)) := by
      intro i p hp
      by_cases h : i < l.length
      · left; exact ⟨h, by rw [List.getElem?_append_left h] at hp; exact hp⟩
      · right
        rw [List.getElem?_append_right (by omega), List.getElem?_singleton] at hp
        split_ifs at hp with h'
        · exact ⟨by omega, (Option.some.inj hp).symm⟩
    constructor
    · intro i p hp
      rcases key i p hp with ⟨_, h⟩ | ⟨_, rfl⟩
      · exact hfin i p h
      · exact hD
    · intro i p q hp hq
      rcases key i p hp with ⟨hi, h⟩ | ⟨hi, rfl⟩ <;> rcases key (i + 1) q hq with ⟨hi', h'⟩ | ⟨hi', rfl⟩
      · exact hmono i p q h h'
      · have hl : l.getLast? = some p := by
          rw [List.getLast?_eq_getElem?, show l.length - 1 = i by omega]; exact h
        exact hτ p.1 (by simp [hl])
      · omega
      · omega
  have hok := hok (Classical.choose h.1) (hs ▸ σ.finite) (hs ▸ σ.mono) hτ
  { seq := .fin (Classical.choose h.1 ++ [(τ, D)])
    finite := hok.1
    mono := hok.2
    progress := fun h => absurd h (by rw [Seq.length]; exact ENat.coe_ne_top _) }

/-- `σ · (τ, D)` as a partial operation: defined iff the result is a trace. -/
noncomputable def snoc? (σ : Trace Sig) (τ : ℕ) (D : DB Sig) : Option (Trace Sig) :=
  open Classical in if h : σ.CanSnoc τ D then some (σ.snoc τ D h) else none

end Trace

/-- The set of all traces `𝒯` (l.497) is the type `Trace Sig`. -/
abbrev Traces := Trace Sig

end Paper
