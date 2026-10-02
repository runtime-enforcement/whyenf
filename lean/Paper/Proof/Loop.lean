/-
  The loops of `Saturate`: `repeat … until unchanged`, passes, sections.
-/
import Paper.Proof.Tables

namespace Paper

open Classical

variable {Voc : Vocabulary}

/-- The state `(Ω, C, S)` of a saturation. -/
abbrev Trip (Voc : Vocabulary) := Set (Obligation Voc) × Set (REv Voc) × Set (REv Voc)

/-- Componentwise inclusion. -/
def Trip.le (x y : Trip Voc) : Prop := x.1 ⊆ y.1 ∧ x.2.1 ⊆ y.2.1 ∧ x.2.2 ⊆ y.2.2

theorem Trip.le_refl (x : Trip Voc) : x.le x := ⟨le_rfl, le_rfl, le_rfl⟩

theorem Trip.le_trans {x y z : Trip Voc} (h1 : x.le y) (h2 : y.le z) : x.le z :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem Trip.le_antisymm {x y : Trip Voc} (h1 : x.le y) (h2 : y.le x) : x = y := by
  obtain ⟨a, b, c⟩ := x; obtain ⟨a', b', c'⟩ := y
  simp only [Trip.le] at h1 h2
  rw [Set.Subset.antisymm h1.1 h2.1, Set.Subset.antisymm h1.2.1 h2.2.1,
    Set.Subset.antisymm h1.2.2 h2.2.2]

/-! ## `repeat … until unchanged` -/

theorem repeat_spec {α : Type} {body : α → α} {x y : α}
    (h : repeatUntilUnchanged body x = some y) : (∃ k, y = body^[k] x) ∧ body y = y := by
  unfold repeatUntilUnchanged at h
  split_ifs at h with hex
  simp only [Option.some.injEq] at h
  subst h
  refine ⟨⟨_, rfl⟩, ?_⟩
  have := Nat.find_spec hex
  rw [← Function.iterate_succ_apply' body]
  rw [Function.iterate_succ_apply', this, ← Function.iterate_succ_apply' body]
  exact this

/-- An inflationary body whose iterates stay in a finite set terminates. -/
theorem repeat_isSome {body : Trip Voc → Trip Voc} {x : Trip Voc}
    (hinf : ∀ z : Trip Voc, z.le (body z)) (F : Set (Trip Voc)) (hF : F.Finite)
    (hin : ∀ k, body^[k] x ∈ F) : (repeatUntilUnchanged body x).isSome := by
  unfold repeatUntilUnchanged
  by_cases hex : ∃ k, body^[k + 1] x = body^[k] x
  · rw [dif_pos hex]; rfl
  · exfalso
    push Not at hex
    have hmono : ∀ k m, k ≤ m → (body^[k] x).le (body^[m] x) := by
      intro k m hkm
      induction m with
      | zero => have : k = 0 := by omega
                subst this; exact Trip.le_refl _
      | succ m ih =>
        rcases Nat.lt_or_eq_of_le hkm with h | h
        · exact Trip.le_trans (ih (by omega)) (by rw [Function.iterate_succ_apply']; exact hinf _)
        · subst h; exact Trip.le_refl _
    have key : ∀ k m, k < m → body^[k] x ≠ body^[m] x := by
      intro k m hkm he
      have h1 : (body^[k] x).le (body^[k + 1] x) := by
        rw [Function.iterate_succ_apply']; exact hinf _
      have h2 := hmono (k + 1) m (by omega)
      rw [← he] at h2
      exact hex k (Trip.le_antisymm h2 h1)
    have hinj : Function.Injective fun k => body^[k] x := by
      intro k m hkm
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact key k m h hkm
      · exact key m k h hkm.symm
    exact Set.infinite_of_injective_forall_mem hinj hin hF

/-! ## Passes -/

section
variable (P : Program Voc) (T : Tables Voc) (τ : ℕ) (D : Set (REv Voc)) (σ : Trace Voc.toSignature)

/-- One rule application. -/
noncomputable def upd (r : Item Voc) (x : Trip Voc) : Trip Voc :=
  Update P r x.1 ⟨T, τ, D, x.2.1, x.2.2⟩ σ

theorem pass_eq (rs : List (Item Voc)) (x : Trip Voc) :
    pass P rs T τ D σ x = rs.foldl (fun x r => upd P T τ D σ r x) x := by
  unfold pass
  induction rs generalizing x with
  | nil => rfl
  | cons r rs ih => obtain ⟨a, b, c⟩ := x; simp only [List.foldl_cons]; exact ih _

theorem upd_infl (r : Item Voc) (x : Trip Voc) : x.le (upd P T τ D σ r x) := by
  obtain ⟨Ω, C, S⟩ := x
  unfold upd Update
  cases r with
  | rule ℓ α p ts delay next c =>
    simp only
    rcases delay with _ | N
    · rcases next with _ | N
      · cases α
        · exact ⟨le_rfl, Set.subset_union_left, le_rfl⟩
        · exact ⟨le_rfl, le_rfl, Set.subset_union_left⟩
      · exact ⟨Set.subset_union_left, le_rfl, le_rfl⟩
    · exact ⟨Set.subset_union_left, le_rfl, le_rfl⟩
  | _ => exact Trip.le_refl _

theorem foldl_infl (rs : List (Item Voc)) (x : Trip Voc) :
    x.le (rs.foldl (fun x r => upd P T τ D σ r x) x) := by
  induction rs generalizing x with
  | nil => exact Trip.le_refl _
  | cons r rs ih => exact Trip.le_trans (upd_infl P T τ D σ r x) (ih _)

theorem pass_infl (rs : List (Item Voc)) (x : Trip Voc) : x.le (pass P rs T τ D σ x) := by
  rw [pass_eq]; exact foldl_infl P T τ D σ rs x

/-- At a fixpoint of a pass, no rule adds anything. -/
theorem pass_fix (rs : List (Item Voc)) (y : Trip Voc) (h : pass P rs T τ D σ y = y) :
    ∀ r ∈ rs, upd P T τ D σ r y = y := by
  rw [pass_eq] at h
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons] at h
    have h1 := upd_infl P T τ D σ r y
    have h2 := foldl_infl P T τ D σ rs (upd P T τ D σ r y)
    rw [h] at h2
    have hz : upd P T τ D σ r y = y := Trip.le_antisymm h2 h1
    rw [hz] at h
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact hz
    · exact ih h r' hr'

/-- The states reachable by applying rules of `rs` in any order. -/
inductive ReachS (rs : List (Item Voc)) (x : Trip Voc) : Trip Voc → Prop
  | refl : ReachS rs x x
  | step {y : Trip Voc} (r : Item Voc) : r ∈ rs → ReachS rs x y → ReachS rs x (upd P T τ D σ r y)

theorem ReachS.trans {rs : List (Item Voc)} {x y z : Trip Voc} (h1 : ReachS P T τ D σ rs x y)
    (h2 : ReachS P T τ D σ rs y z) : ReachS P T τ D σ rs x z := by
  induction h2 with
  | refl => exact h1
  | step r hr _ ih => exact .step r hr ih

theorem ReachS.foldl {rs : List (Item Voc)} {x : Trip Voc} :
    ∀ (l : List (Item Voc)), (∀ r ∈ l, r ∈ rs) → ∀ y, ReachS P T τ D σ rs x y →
      ReachS P T τ D σ rs x (l.foldl (fun x r => upd P T τ D σ r x) y)
  | [], _, y, h => h
  | r :: l, hl, y, h => by
    simp only [List.foldl_cons]
    exact ReachS.foldl l (fun r' hr' => hl r' (by simp [hr'])) _ (.step r (hl r (by simp)) h)

theorem ReachS.le {rs : List (Item Voc)} {x y : Trip Voc} (h : ReachS P T τ D σ rs x y) : x.le y := by
  induction h with
  | refl => exact Trip.le_refl _
  | step r _ _ ih => exact Trip.le_trans ih (upd_infl P T τ D σ r _)

theorem repeat_pass {rs : List (Item Voc)} {x y : Trip Voc}
    (h : repeatUntilUnchanged (pass P rs T τ D σ) x = some y) :
    ReachS P T τ D σ rs x y ∧ pass P rs T τ D σ y = y := by
  obtain ⟨⟨k, rfl⟩, hfix⟩ := repeat_spec h
  refine ⟨?_, hfix⟩
  clear hfix h
  induction k with
  | zero => exact .refl
  | succ k ih =>
    rw [Function.iterate_succ_apply', pass_eq]
    exact ReachS.foldl P T τ D σ rs (fun r hr => hr) _ ih

/-- A run of the sections. -/
inductive RunSecs : List (SecKind × List (Item Voc)) → Trip Voc → Trip Voc → Prop
  | nil (x : Trip Voc) : RunSecs [] x x
  | cons {s : SecKind × List (Item Voc)} {ss : List (SecKind × List (Item Voc))} {x y z : Trip Voc} :
      ReachS P T τ D σ s.2 x y → pass P s.2 T τ D σ y = y → RunSecs ss y z → RunSecs (s :: ss) x z

theorem runSections_spec : ∀ (ss : List (SecKind × List (Item Voc))), (∀ s ∈ ss, s.1 = .fixpoint) →
    ∀ x z, runSections P ss T τ D σ x = some z → RunSecs P T τ D σ ss x z
  | [], _, x, z, h => by simp [runSections] at h; subst h; exact .nil x
  | s :: ss, hs, x, z, h => by
    simp only [runSections, Option.bind_eq_some_iff] at h
    obtain ⟨y, h1, h2⟩ := h
    have hk := hs s (by simp)
    unfold runSection at h1
    rw [hk] at h1
    obtain ⟨r1, r2⟩ := repeat_pass P T τ D σ h1
    exact .cons r1 r2 (runSections_spec ss (fun s' hs' => hs s' (by simp [hs'])) y z h2)

theorem RunSecs.le {ss : List (SecKind × List (Item Voc))} {x z : Trip Voc}
    (h : RunSecs P T τ D σ ss x z) : x.le z := by
  induction h with
  | nil => exact Trip.le_refl _
  | cons h1 _ _ ih => exact Trip.le_trans (h1.le P T τ D σ) ih

end

end Paper
