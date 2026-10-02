/-
  Lemmas about traces (§2.1).
-/
import Paper.Traces

namespace Paper

namespace Seq
variable {α : Type}

theorem get?_isSome_iff (s : Seq α) (i : ℕ) : (s.get? i).isSome ↔ (i : ℕ∞) < s.length := by
  cases s with
  | fin l => simp [get?, length]
  | inf f => simp [get?, length]

end Seq

namespace Trace
variable {Sig : Signature}

theorem lastTs?_of_fin {σ : Trace Sig} {l} (hs : σ.seq = .fin l) :
    σ.lastTs? = l.getLast?.map Prod.fst := by
  unfold lastTs?; rw [hs]

end Trace

end Paper
