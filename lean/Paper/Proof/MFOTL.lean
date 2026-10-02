/-
  Lemmas about intervals (§2.2).
-/
import Paper.MFOTL
import Paper.Proof.Traces

namespace Paper

namespace Interval

@[simp] theorem mem_icc {a b h n} : n ∈ icc a b h ↔ a ≤ n ∧ (n : ℕ∞) ≤ b := Iff.rfl

@[simp] theorem mem_univ (n : ℕ) : n ∈ univ := by simp [univ]

/-- Every non-empty interval of `ℕ` is `[a, b]` for some `a ≤ b ∈ ℕ ∪ {∞}`.
    (So intervals given by bounds, as used from §3 on, are all intervals.) -/
theorem eq_icc (I : Interval) : ∃ a b h, I = icc a b h := by
  classical
  obtain ⟨⟨n, hn⟩, hc⟩ := I.2
  let a := Nat.find (⟨n, hn⟩ : ∃ n, n ∈ I.1)
  have ha : a ∈ I.1 := Nat.find_spec (⟨n, hn⟩ : ∃ n, n ∈ I.1)
  have hamin : ∀ m ∈ I.1, a ≤ m := fun m hm => Nat.find_min' _ hm
  by_cases hb : BddAbove I.1
  · obtain ⟨B, hB⟩ := hb
    have hex : ∃ m, m ∈ I.1 ∧ ∀ k ∈ I.1, k ≤ m := by
      have hfin : I.1.Finite := (Set.finite_Iic B).subset hB
      obtain ⟨m, hm, hmax⟩ := hfin.exists_maximal ⟨a, ha⟩
      exact ⟨m, hm, fun k hk => by
        by_contra h; push Not at h; exact absurd (hmax hk h.le) (by omega)⟩
    obtain ⟨b, hbI, hbmax⟩ := hex
    refine ⟨a, b, Nat.cast_le.2 (hamin b hbI), Subtype.ext ?_⟩
    ext m; simp only [icc, Set.mem_setOf_eq, Nat.cast_le]
    exact ⟨fun hm => ⟨hamin m hm, hbmax m hm⟩, fun hm => hc.out ha hbI hm⟩
  · refine ⟨a, ⊤, le_top, Subtype.ext ?_⟩
    ext m; simp only [icc, Set.mem_setOf_eq, le_top, and_true]
    refine ⟨fun hm => hamin m hm, fun hm => ?_⟩
    rw [not_bddAbove_iff] at hb
    obtain ⟨k, hk, hmk⟩ := hb m
    exact hc.out ha hk ⟨hm, hmk.le⟩

end Interval

end Paper
