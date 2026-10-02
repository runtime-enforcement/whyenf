/-
  Lemmas about the enforcer of a program (§4.6).
-/
import Paper.Compile

namespace Paper

variable {Voc : Vocabulary}

theorem REv.toDB_mem {A : Set (REv Voc)} {E : Set Voc.ℰ} (h : REv.InDB A E) :
    REv.toDB A ∈ DBOf Voc.toSignature E := fun _ hev => (h _ hev).1

end Paper
