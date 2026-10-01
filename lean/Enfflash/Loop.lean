/-
  Enfflash formalization — the enforcement loop as a program (paper,
  Algorithm 1 with `μ` and `ν` from Algorithm 2).

  The loop processes the input trace block by block: for input time-point
  `k`, it calls `μ` (reactive) and then `ν(t)` (proactive) for every timestamp
  `t` from `τ_k` up to `τ_{k+1} - 1`.  A cursor enumerates these calls, so the
  loop is a function `run : ℕ → LState`.  Its state holds the table state,
  the pending obligations `Ω` (with timestamp or time-point deadlines), and
  the number of output time-points so far; each call may produce an output
  time-point.

  `loopRun`: the output of the loop is a `LoopRun` (in particular, delayed
  and next obligations are discharged on time), and its timestamps are
  monotone.  Together with `enforcer_sound_*`, this closes the gap between
  the loop specification and the loop program.
-/
import Enfflash.Conflict

namespace Enfflash

universe u
variable {B L D : Type u}

open Classical

/-- Deadlines of obligations: a timestamp (`[delay]`) or a time-point
    (`[next]`). -/
inductive Deadline where
  | ts : ℕ → Deadline
  | tp : ℕ → Deadline

/-- The loop's cursor: the reactive call for input `k`, or the proactive call
    at timestamp `t` after input `k`. -/
inductive Cur where
  | react : ℕ → Cur
  | pro : ℕ → ℕ → Cur

/-- An output time-point with the data of its `Saturate` run. -/
structure Point (B L D : Type u) where
  ts : ℕ
  K : Ctx B L D
  D₀ : DB B L D
  init : Set (Act B L D)
  X : Set (Act B L D)

/-- Parameters of the loop: the input trace, the EF program, the table state
    (abstractly: the let interpretation it induces and its update after each
    time-point), and a saturation function computing a `Saturate` run. -/
structure LoopParams (B L D : Type u) where
  τ : ℕ → ℕ
  inDB : ℕ → DB B L D
  P : Program B L D
  TS : Type u
  tab₀ : TS
  /-- an invariant of reachable table states (e.g. finiteness) -/
  inv : TS → Prop
  ctx : TS → ℕ → Ctx B L D
  commit : TS → ℕ → DB B L D → TS
  Sat : Ctx B L D → DB B L D → Set (Act B L D) → Set (Act B L D)

structure LState (B L D : Type u) (TS : Type u) where
  cur : Cur
  tab : TS
  Ω : Set ((Ev B L × List D) × Deadline)
  len : ℕ

namespace LoopParams
variable (Q : LoopParams B L D)

/-- Obligations created by the actions of a time-point with index `len` and
    timestamp `t`. -/
def oblOf (len t : ℕ) : Act B L D → Set ((Ev B L × List D) × Deadline)
  | .later b x => {(x, .ts (t + b))}
  | .next n _ x => {(x, .tp (len + n))}
  | _ => ∅

def newObl (len t : ℕ) (X : Set (Act B L D)) : Set ((Ev B L × List D) × Deadline) :=
  ⋃ a ∈ X, oblOf len t a

/-- `next` obligations due at the time-point with index `len`. -/
def dueTp (s : LState B L D Q.TS) : Set (Act B L D) :=
  {a | ∃ x, a = .cau x ∧ (x, Deadline.tp s.len) ∈ s.Ω}

/-- `delay` obligations due at timestamp `t`. -/
def dueTs (s : LState B L D Q.TS) (t : ℕ) : Set (Act B L D) :=
  {a | ∃ x, a = .cau x ∧ (x, Deadline.ts t) ∈ s.Ω}

/-- Produce a time-point: run `Saturate`, register new obligations, commit
    the tables. -/
noncomputable def produce (s : LState B L D Q.TS) (t : ℕ) (D₀ : DB B L D)
    (init : Set (Act B L D)) : LState B L D Q.TS × Point B L D :=
  let K := Q.ctx s.tab t
  let X := Q.Sat K D₀ init
  (⟨s.cur, Q.commit s.tab t (work D₀ X), s.Ω ∪ newObl s.len t X, s.len + 1⟩,
    ⟨t, K, D₀, init, X⟩)

/-- One call of the loop: `μ(k)`, `ν(t)`, or moving to the next block. -/
noncomputable def step (s : LState B L D Q.TS) : LState B L D Q.TS × Option (Point B L D) :=
  match s.cur with
  | .react k =>
    let r := Q.produce s (Q.τ k) (Q.inDB k) (Q.dueTp s)
    (⟨.pro k (Q.τ k), r.1.tab, r.1.Ω, r.1.len⟩, some r.2)
  | .pro k t =>
    if t < Q.τ (k + 1) then
      let C := Q.dueTp s ∪ Q.dueTs s t
      if C.Nonempty then
        let r := Q.produce s t ∅ C
        (⟨.pro k (t + 1), r.1.tab, r.1.Ω, r.1.len⟩, some r.2)
      else (⟨.pro k (t + 1), s.tab, s.Ω, s.len⟩, none)
    else (⟨.react (k + 1), s.tab, s.Ω, s.len⟩, none)

/-- The state after `n` calls. -/
noncomputable def run : ℕ → LState B L D Q.TS
  | 0 => ⟨.react 0, Q.tab₀, ∅, 0⟩
  | n + 1 => (Q.step (run n)).1

/-- The time-point produced by call `n`, if any. -/
noncomputable def prod (n : ℕ) : Option (Point B L D) := (Q.step (Q.run n)).2

/-- The timestamp of a call. -/
def curTs : Cur → ℕ
  | .react k => Q.τ k
  | .pro _ t => t

end LoopParams

/-! ## Assumptions on the parameters -/

/-- Well-formed loop parameters. -/
structure LoopParams.Wf (Q : LoopParams B L D) (v₀ : ℕ → D) : Prop where
  mono : Monotone Q.τ
  progress : ∀ t, ∃ k, t < Q.τ k
  finDB : ∀ k, (Q.inDB k).Finite
  hv₀ : ∀ s t, (Q.ctx s t).v₀ = v₀
  inv₀ : Q.inv Q.tab₀
  invCommit : ∀ s t (W : DB B L D), Q.inv s → W.Finite → Q.inv (Q.commit s t W)
  sat : ∀ s t (D₀ : DB B L D) X, Q.inv s → D₀.Finite → X.Finite →
    SatRun (Q.ctx s t) D₀ Q.P.secs X (Q.Sat (Q.ctx s t) D₀ X) ∧ (Q.Sat (Q.ctx s t) D₀ X).Finite
  later : ∀ c ∈ Q.P.rules, ∀ b e ts, c.eff = .later b e ts → 1 ≤ b
  next : ∀ c ∈ Q.P.rules, ∀ n t e ts, c.eff = .next n t e ts → 1 ≤ n ∧ (t = true → n = 1)

namespace LoopParams
variable {Q : LoopParams B L D}

/-! ## The calls -/

theorem step_react {s : LState B L D Q.TS} {k : ℕ} (h : s.cur = .react k) :
    Q.step s = (⟨.pro k (Q.τ k), (Q.produce s (Q.τ k) (Q.inDB k) (Q.dueTp s)).1.tab,
      (Q.produce s (Q.τ k) (Q.inDB k) (Q.dueTp s)).1.Ω, s.len + 1⟩,
      some (Q.produce s (Q.τ k) (Q.inDB k) (Q.dueTp s)).2) := by
  simp only [step, h]; rfl

theorem step_pro_prod {s : LState B L D Q.TS} {k t : ℕ} (h : s.cur = .pro k t)
    (ht : t < Q.τ (k + 1)) (hC : (Q.dueTp s ∪ Q.dueTs s t).Nonempty) :
    Q.step s = (⟨.pro k (t + 1), (Q.produce s t ∅ (Q.dueTp s ∪ Q.dueTs s t)).1.tab,
      (Q.produce s t ∅ (Q.dueTp s ∪ Q.dueTs s t)).1.Ω, s.len + 1⟩,
      some (Q.produce s t ∅ (Q.dueTp s ∪ Q.dueTs s t)).2) := by
  simp only [step, h, ht, if_true, hC]; rfl

theorem step_pro_none {s : LState B L D Q.TS} {k t : ℕ} (h : s.cur = .pro k t)
    (ht : t < Q.τ (k + 1)) (hC : ¬ (Q.dueTp s ∪ Q.dueTs s t).Nonempty) :
    Q.step s = (⟨.pro k (t + 1), s.tab, s.Ω, s.len⟩, none) := by
  simp only [step, h, ht, if_true, hC, if_false]

theorem step_next {s : LState B L D Q.TS} {k t : ℕ} (h : s.cur = .pro k t)
    (ht : ¬ t < Q.τ (k + 1)) : Q.step s = (⟨.react (k + 1), s.tab, s.Ω, s.len⟩, none) := by
  simp only [step, h, ht, if_false]

/-- What a produced time-point looks like. -/
structure Produced (s : LState B L D Q.TS) (p : Point B L D) (s' : LState B L D Q.TS) : Prop where
  len : s'.len = s.len + 1
  Ω : s'.Ω = s.Ω ∪ newObl s.len p.ts p.X
  tab : s'.tab = Q.commit s.tab p.ts (work p.D₀ p.X)
  ts : p.ts = Q.curTs s.cur
  K : p.K = Q.ctx s.tab p.ts
  X : p.X = Q.Sat p.K p.D₀ p.init
  D₀ : (∃ k, s.cur = .react k ∧ p.D₀ = Q.inDB k) ∨ p.D₀ = ∅
  initTp : Q.dueTp s ⊆ p.init
  initTs : ∀ k t, s.cur = .pro k t → Q.dueTs s t ⊆ p.init
  initSub : p.init ⊆ Q.dueTp s ∪ Q.dueTs s p.ts

theorem step_cases (s : LState B L D Q.TS) :
    ((Q.step s).2 = none ∧ (Q.step s).1.len = s.len ∧ (Q.step s).1.Ω = s.Ω ∧
      (Q.step s).1.tab = s.tab) ∨
    ∃ p, (Q.step s).2 = some p ∧ Q.Produced s p (Q.step s).1 := by
  rcases hc : s.cur with k | ⟨k, t⟩
  · rw [step_react hc]
    refine Or.inr ⟨_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, Or.inl ⟨k, hc, rfl⟩, fun _ h => h,
      fun k' t' h => ?_, fun _ h => Or.inl h⟩
    · simp [produce]
    · simp [curTs, hc, produce]
    · rw [hc] at h; cases h
  · by_cases ht : t < Q.τ (k + 1)
    · by_cases hC : (Q.dueTp s ∪ Q.dueTs s t).Nonempty
      · rw [step_pro_prod hc ht hC]
        refine Or.inr ⟨_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, Or.inr rfl, fun _ h => Or.inl h,
          fun k' t' h => ?_, fun _ h => ?_⟩
        · simp [produce]
        · simp [curTs, hc, produce]
        · rw [hc] at h; cases h; exact fun _ h => Or.inr h
        · simpa [curTs, hc, produce] using h
      · rw [step_pro_none hc ht hC]; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    · rw [step_next hc ht]; exact Or.inl ⟨rfl, rfl, rfl, rfl⟩

theorem run_succ (n : ℕ) : Q.run (n + 1) = (Q.step (Q.run n)).1 := rfl

theorem prod_cases (n : ℕ) :
    (Q.prod n = none ∧ (Q.run (n + 1)).len = (Q.run n).len ∧ (Q.run (n + 1)).Ω = (Q.run n).Ω ∧
      (Q.run (n + 1)).tab = (Q.run n).tab) ∨
    ∃ p, Q.prod n = some p ∧ Q.Produced (Q.run n) p (Q.run (n + 1)) :=
  step_cases (Q.run n)

/-! ## Invariants -/

theorem len_mono : Monotone fun n => (Q.run n).len := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases prod_cases (Q := Q) n with ⟨-, h, -, -⟩ | ⟨p, -, hp⟩
  · exact h.ge
  · simp only [hp.len]; omega

theorem Ω_mono : Monotone fun n => (Q.run n).Ω := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases prod_cases (Q := Q) n with ⟨-, -, h, -⟩ | ⟨p, -, hp⟩
  · exact h.ge
  · simp only [hp.Ω]; exact Set.subset_union_left

/-- The cursor stays within its block. -/
theorem cur_inv (hQ : Q.Wf v₀) : ∀ n, ∀ k t, (Q.run n).cur = .pro k t → Q.τ k ≤ t ∧ t ≤ Q.τ (k + 1)
  | 0, k, t, h => by simp [run] at h
  | n + 1, k, t, h => by
    rw [run_succ] at h
    rcases hc : (Q.run n).cur with k' | ⟨k', t'⟩
    · rw [step_react hc] at h; cases h
      exact ⟨le_rfl, hQ.mono (Nat.le_succ k)⟩
    · have ih := cur_inv hQ n k' t' hc
      by_cases ht : t' < Q.τ (k' + 1)
      · by_cases hC : (Q.dueTp (Q.run n) ∪ Q.dueTs (Q.run n) t').Nonempty
        · rw [step_pro_prod hc ht hC] at h; cases h; exact ⟨by omega, by omega⟩
        · rw [step_pro_none hc ht hC] at h; cases h; exact ⟨by omega, by omega⟩
      · rw [step_next hc ht] at h; cases h

/-- Call timestamps are monotone. -/
theorem curTs_succ (hQ : Q.Wf v₀) (n : ℕ) :
    Q.curTs (Q.run n).cur ≤ Q.curTs (Q.run (n + 1)).cur := by
  rw [run_succ]
  rcases hc : (Q.run n).cur with k | ⟨k, t⟩
  · rw [step_react hc]; simp [curTs]
  · by_cases ht : t < Q.τ (k + 1)
    · by_cases hC : (Q.dueTp (Q.run n) ∪ Q.dueTs (Q.run n) t).Nonempty
      · rw [step_pro_prod hc ht hC]; simp [curTs]
      · rw [step_pro_none hc ht hC]; simp [curTs]
    · rw [step_next hc ht]; simp only [curTs]
      have := (cur_inv hQ n k t hc).2; omega

theorem curTs_mono (hQ : Q.Wf v₀) : Monotone fun n => Q.curTs (Q.run n).cur :=
  monotone_nat_of_le_succ (curTs_succ hQ)

/-- After the proactive call at `t` (within its block), the timestamp moves on. -/
theorem curTs_after_pro (hQ : Q.Wf v₀) {n k t : ℕ} (hc : (Q.run n).cur = .pro k t)
    (ht : t < Q.τ (k + 1)) : ∀ m, n < m → t < Q.curTs (Q.run m).cur := by
  have h1 : Q.curTs (Q.run (n + 1)).cur = t + 1 := by
    rw [run_succ]
    by_cases hC : (Q.dueTp (Q.run n) ∪ Q.dueTs (Q.run n) t).Nonempty
    · rw [step_pro_prod hc ht hC]; rfl
    · rw [step_pro_none hc ht hC]; rfl
  intro m hm
  have := curTs_mono hQ (show n + 1 ≤ m by omega)
  simp only at this; omega

/-! ## Reachability -/

theorem pro_walk (hQ : Q.Wf v₀) {n k t : ℕ} (hc : (Q.run n).cur = .pro k t) :
    ∀ d, t + d ≤ Q.τ (k + 1) → (Q.run (n + d)).cur = .pro k (t + d)
  | 0, _ => hc
  | d + 1, hd => by
    have ih := pro_walk hQ hc d (by omega)
    rw [show n + (d + 1) = n + d + 1 by omega, run_succ]
    have ht : t + d < Q.τ (k + 1) := by omega
    by_cases hC : (Q.dueTp (Q.run (n + d)) ∪ Q.dueTs (Q.run (n + d)) (t + d)).Nonempty
    · rw [step_pro_prod ih ht hC]; rfl
    · rw [step_pro_none ih ht hC]; rfl

/-- Every reactive call happens, with at least `k` time-points produced
    before it. -/
theorem react_reached (hQ : Q.Wf v₀) : ∀ k, ∃ n, (Q.run n).cur = .react k ∧ k ≤ (Q.run n).len
  | 0 => ⟨0, rfl, Nat.zero_le _⟩
  | k + 1 => by
    obtain ⟨n, hn, hlen⟩ := react_reached hQ k
    have h1 : (Q.run (n + 1)).cur = .pro k (Q.τ k) := by rw [run_succ, step_react hn]
    have hl1 : (Q.run (n + 1)).len = (Q.run n).len + 1 := by rw [run_succ, step_react hn]
    set d := Q.τ (k + 1) - Q.τ k
    have hmono := hQ.mono (show k ≤ k + 1 by omega)
    have h2 := pro_walk hQ h1 d (by omega)
    rw [show Q.τ k + d = Q.τ (k + 1) by omega] at h2
    refine ⟨n + 1 + d + 1, ?_, ?_⟩
    · rw [run_succ, step_next h2 (lt_irrefl _)]
    · have := len_mono (Q := Q) (show n + 1 ≤ n + 1 + d + 1 by omega)
      simp only at this; omega

/-- Every proactive call `ν(T)` with `T ≥ τ₀` happens. -/
theorem pro_reached (hQ : Q.Wf v₀) {T : ℕ} (hT : Q.τ 0 ≤ T) :
    ∃ n k, (Q.run n).cur = .pro k T ∧ T < Q.τ (k + 1) := by
  have hex : ∃ m, T < Q.τ m := hQ.progress T
  set m := Nat.find hex
  have hm : T < Q.τ m := Nat.find_spec hex
  have hm0 : m ≠ 0 := fun h => by rw [h] at hm; omega
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hkT : Q.τ k ≤ T := by
    have := Nat.find_min hex (show k < m by omega); omega
  obtain ⟨n, hn, -⟩ := react_reached hQ k
  have h1 : (Q.run (n + 1)).cur = .pro k (Q.τ k) := by rw [run_succ, step_react hn]
  have h2 := pro_walk hQ h1 (T - Q.τ k) (by rw [← hk]; omega)
  rw [show Q.τ k + (T - Q.τ k) = T by omega] at h2
  exact ⟨_, k, h2, hk ▸ hm⟩

/-! ## Output time-points -/

theorem len_unbounded (hQ : Q.Wf v₀) (j : ℕ) : ∃ n, j < (Q.run (n + 1)).len := by
  obtain ⟨n, hn, hlen⟩ := react_reached hQ (j + 1)
  refine ⟨n, ?_⟩
  have := len_mono (Q := Q) (show n ≤ n + 1 by omega); simp only at this; omega

/-- The call producing time-point `j`. -/
noncomputable def cstep (hQ : Q.Wf v₀) (j : ℕ) : ℕ := Nat.find (len_unbounded hQ j)

theorem cstep_spec (hQ : Q.Wf v₀) (j : ℕ) :
    (Q.run (cstep hQ j)).len = j ∧ ∃ p, Q.prod (cstep hQ j) = some p ∧
      Q.Produced (Q.run (cstep hQ j)) p (Q.run (cstep hQ j + 1)) := by
  have h1 : j < (Q.run (cstep hQ j + 1)).len := Nat.find_spec (len_unbounded hQ j)
  have h0 : (Q.run (cstep hQ j)).len ≤ j := by
    rcases hc : cstep hQ j with _ | m
    · simp [run]
    · have := Nat.find_min (len_unbounded hQ j) (show m < cstep hQ j by omega)
      rw [hc] at *; omega
  rcases prod_cases (Q := Q) (cstep hQ j) with ⟨-, hl, -, -⟩ | ⟨p, hp, hpr⟩
  · omega
  · exact ⟨by have := hpr.len; omega, p, hp, hpr⟩

/-- The output time-point `j`. -/
noncomputable def pt (hQ : Q.Wf v₀) (j : ℕ) : Point B L D :=
  Classical.choose (cstep_spec hQ j).2

theorem pt_spec (hQ : Q.Wf v₀) (j : ℕ) :
    Q.prod (cstep hQ j) = some (pt hQ j) ∧
      Q.Produced (Q.run (cstep hQ j)) (pt hQ j) (Q.run (cstep hQ j + 1)) :=
  Classical.choose_spec (cstep_spec hQ j).2

/-- Producing calls are exactly the `cstep`s. -/
theorem cstep_unique (hQ : Q.Wf v₀) {n : ℕ} {p : Point B L D} (hp : Q.prod n = some p) :
    n = cstep hQ (Q.run n).len ∧ p = pt hQ (Q.run n).len := by
  set j := (Q.run n).len
  have hn1 : (Q.run (n + 1)).len = j + 1 := by
    rcases prod_cases (Q := Q) n with ⟨h, -, -, -⟩ | ⟨p', hp', hpr⟩
    · rw [hp] at h; cases h
    · exact hpr.len
  obtain ⟨hc, -⟩ := cstep_spec hQ j
  have hc1 : (Q.run (cstep hQ j + 1)).len = j + 1 := by
    obtain ⟨-, p', -, hpr⟩ := cstep_spec hQ j; rw [hpr.len, hc]
  have heq : n = cstep hQ j := by
    rcases lt_trichotomy n (cstep hQ j) with h | h | h
    · have := len_mono (Q := Q) (show n + 1 ≤ cstep hQ j by omega); simp only at this; omega
    · exact h
    · have := len_mono (Q := Q) (show cstep hQ j + 1 ≤ n by omega); simp only at this; omega
  refine ⟨heq, ?_⟩
  have := (pt_spec hQ j).1
  rw [← heq, hp] at this; exact Option.some.inj this

theorem cstep_strictMono (hQ : Q.Wf v₀) : StrictMono (cstep (Q := Q) hQ) := by
  intro i j hij
  by_contra h
  have := len_mono (Q := Q) (show cstep hQ j ≤ cstep hQ i by omega)
  simp only [(cstep_spec hQ i).1, (cstep_spec hQ j).1] at this; omega

theorem pt_ts (hQ : Q.Wf v₀) (j : ℕ) : (pt hQ j).ts = Q.curTs (Q.run (cstep hQ j)).cur :=
  (pt_spec hQ j).2.ts

theorem pt_ts_mono (hQ : Q.Wf v₀) : Monotone fun j => (pt hQ j).ts := by
  intro i j hij
  simp only [pt_ts]
  exact curTs_mono hQ ((cstep_strictMono hQ).monotone hij)

/-- Output timestamps start at `τ₀`. -/
theorem curTs_ge (hQ : Q.Wf v₀) (n : ℕ) : Q.τ 0 ≤ Q.curTs (Q.run n).cur :=
  curTs_mono hQ (Nat.zero_le n)

/-! ## Obligations -/

theorem dueTp_sub (s : LState B L D Q.TS) : Q.dueTp s ⊆ (fun o => Act.cau o.1) '' s.Ω := by
  rintro a ⟨x, rfl, hx⟩; exact ⟨_, hx, rfl⟩

theorem dueTs_sub (s : LState B L D Q.TS) (t : ℕ) :
    Q.dueTs s t ⊆ (fun o => Act.cau o.1) '' s.Ω := by
  rintro a ⟨x, rfl, hx⟩; exact ⟨_, hx, rfl⟩

theorem newObl_finite (len t : ℕ) {X : Set (Act B L D)} (hX : X.Finite) :
    (newObl len t X).Finite :=
  hX.biUnion fun a _ => by cases a <;> simp [oblOf]

theorem work_finite {D₀ : DB B L D} {X : Set (Act B L D)} (hD : D₀.Finite) (hX : X.Finite) :
    (work D₀ X).Finite := by
  refine (hD.union (hX.preimage (fun _ _ _ _ h => Act.cau.inj h))).subset ?_
  rintro x (⟨hx, -⟩ | hx)
  exacts [Or.inl hx, Or.inr hx]

/-- Reachable table states satisfy the invariant, and pending obligations are
    finite. -/
theorem state_ok (hQ : Q.Wf v₀) : ∀ n, Q.inv (Q.run n).tab ∧ (Q.run n).Ω.Finite
  | 0 => ⟨hQ.inv₀, Set.finite_empty⟩
  | n + 1 => by
    obtain ⟨hinv, hΩ⟩ := state_ok hQ n
    rcases prod_cases (Q := Q) n with ⟨-, -, h, ht⟩ | ⟨p, -, hp⟩
    · rw [h, ht]; exact ⟨hinv, hΩ⟩
    · have hD : p.D₀.Finite := by
        rcases hp.D₀ with ⟨k, -, h⟩ | h <;> rw [h]
        exacts [hQ.finDB k, Set.finite_empty]
      have hinit : p.init.Finite := ((hΩ.image _).union (hΩ.image _)).subset
        (hp.initSub.trans (Set.union_subset_union (dueTp_sub _) (dueTs_sub _ _)))
      have hX : p.X.Finite := by
        rw [hp.X, hp.K]; exact (hQ.sat _ _ _ _ hinv hD hinit).2
      rw [hp.tab, hp.Ω]
      exact ⟨hQ.invCommit _ _ _ hinv (work_finite hD hX), hΩ.union (newObl_finite _ _ hX)⟩

theorem Ω_finite (hQ : Q.Wf v₀) (n : ℕ) : (Q.run n).Ω.Finite := (state_ok hQ n).2

theorem pt_finite (hQ : Q.Wf v₀) (j : ℕ) : (pt hQ j).D₀.Finite ∧ (pt hQ j).init.Finite := by
  have hp := (pt_spec hQ j).2
  refine ⟨?_, ?_⟩
  · rcases hp.D₀ with ⟨k, -, h⟩ | h <;> rw [h]
    exacts [hQ.finDB k, Set.finite_empty]
  · exact (((Ω_finite hQ _).image _).union ((Ω_finite hQ _).image _)).subset
      (hp.initSub.trans (Set.union_subset_union (dueTp_sub _) (dueTs_sub _ _)))

/-- Every pending obligation was created by an earlier produced time-point. -/
theorem Ω_src : ∀ n, ∀ o ∈ (Q.run n).Ω, ∃ m < n, ∃ p, Q.prod m = some p ∧
    o ∈ newObl (Q.run m).len p.ts p.X
  | 0, o, h => by simp [run] at h
  | n + 1, o, h => by
    rcases prod_cases (Q := Q) n with ⟨-, -, hΩ, -⟩ | ⟨p, hp, hpr⟩
    · rw [hΩ] at h
      obtain ⟨m, hm, rest⟩ := Ω_src n o h; exact ⟨m, by omega, rest⟩
    · rw [hpr.Ω] at h
      rcases h with h | h
      · obtain ⟨m, hm, rest⟩ := Ω_src n o h; exact ⟨m, by omega, rest⟩
      · exact ⟨n, by omega, p, hp, h⟩

/-! ## The output trace -/

/-- The output trace of the loop. -/
noncomputable def outTr (hQ : Q.Wf v₀) : Tr B L D where
  db j := work (pt hQ j).D₀ (pt hQ j).X
  ts j := (pt hQ j).ts
  lv j := (pt hQ j).K.lv (work (pt hQ j).D₀ (pt hQ j).X)

theorem pt_satRun (hQ : Q.Wf v₀) (j : ℕ) :
    SatRun (pt hQ j).K (pt hQ j).D₀ Q.P.secs (pt hQ j).init (pt hQ j).X := by
  have hp := (pt_spec hQ j).2
  have hfin := pt_finite hQ j
  have := (hQ.sat (Q.run (cstep hQ j)).tab (pt hQ j).ts (pt hQ j).D₀ (pt hQ j).init
    (state_ok hQ _).1 hfin.1 hfin.2).1
  rw [← hp.K, ← hp.X] at this; exact this

/-- The initial actions of a time-point are causations. -/
theorem init_cau (hQ : Q.Wf v₀) (j : ℕ) : ∀ a ∈ (pt hQ j).init, ∃ x, a = Act.cau x ∧
    ∃ dl, (x, dl) ∈ (Q.run (cstep hQ j)).Ω := by
  intro a ha
  rcases (pt_spec hQ j).2.initSub ha with ⟨x, rfl, hx⟩ | ⟨x, rfl, hx⟩
  exacts [⟨x, rfl, _, hx⟩, ⟨x, rfl, _, hx⟩]

/-- Deferred actions come from rules, hence respect the program's bounds. -/
theorem deferred_bounds (hQ : Q.Wf v₀) (j : ℕ) :
    (∀ b x, Act.later b x ∈ (pt hQ j).X → 1 ≤ b) ∧
    (∀ n t x, Act.next n t x ∈ (pt hQ j).X → 1 ≤ n ∧ (t = true → n = 1)) := by
  have hsrc := (pt_satRun hQ j).fires_src
  constructor
  · intro b x hx
    rcases hsrc _ hx with h | ⟨sec, hsec, c, hc, W, ds, -, -, he⟩
    · obtain ⟨y, hy, -⟩ := init_cau hQ j _ h; cases hy
    · have hcr : c ∈ Q.P.rules := List.mem_flatten.2 ⟨sec, hsec, hc⟩
      cases hce : c.eff <;> rw [hce] at he <;> simp [Effect.act] at he
      obtain ⟨rfl, -⟩ := he
      exact hQ.later c hcr _ _ _ hce
  · intro n t x hx
    rcases hsrc _ hx with h | ⟨sec, hsec, c, hc, W, ds, -, -, he⟩
    · obtain ⟨y, hy, -⟩ := init_cau hQ j _ h; cases hy
    · have hcr : c ∈ Q.P.rules := List.mem_flatten.2 ⟨sec, hsec, hc⟩
      cases hce : c.eff <;> rw [hce] at he <;> simp [Effect.act] at he
      obtain ⟨rfl, rfl, -⟩ := he
      exact hQ.next c hcr _ _ _ _ hce

theorem obl_after (hQ : Q.Wf v₀) {i : ℕ} {o} (ho : o ∈ newObl i (pt hQ i).ts (pt hQ i).X) :
    ∀ n, cstep hQ i < n → o ∈ (Q.run n).Ω := by
  intro n hn
  have hΩ := (pt_spec hQ i).2.Ω
  have h1 : o ∈ (Q.run (cstep hQ i + 1)).Ω := by
    rw [hΩ, (cstep_spec hQ i).1]; exact Or.inr ho
  exact Ω_mono (Q := Q) (show cstep hQ i + 1 ≤ n by omega) h1

/-- A proactive call with something due produces a time-point. -/
theorem pro_produces {n k t : ℕ} (hc : (Q.run n).cur = .pro k t) (ht : t < Q.τ (k + 1))
    (hC : (Q.dueTp (Q.run n) ∪ Q.dueTs (Q.run n) t).Nonempty) :
    ∃ p, Q.prod n = some p ∧ Q.Produced (Q.run n) p (Q.run (n + 1)) := by
  rcases prod_cases (Q := Q) n with ⟨h, -, -, -⟩ | h
  · simp only [prod] at h; rw [step_pro_prod hc ht hC] at h; cases h
  · exact h

theorem react_produces {n k : ℕ} (hc : (Q.run n).cur = .react k) :
    ∃ p, Q.prod n = some p ∧ Q.Produced (Q.run n) p (Q.run (n + 1)) := by
  rcases prod_cases (Q := Q) n with ⟨h, -, -, -⟩ | h
  · simp only [prod] at h; rw [step_react hc] at h; cases h
  · exact h

/-- **`delay` obligations are discharged at the proactive time-point for
    their deadline.** -/
theorem laterFire (hQ : Q.Wf v₀) (i b : ℕ) (x : Ev B L × List D)
    (hx : Act.later b x ∈ (pt hQ i).X) :
    ∃ j, Effect.lastAt (outTr hQ) ((outTr hQ).ts i + b) j ∧ Act.cau x ∈ (pt hQ j).init := by
  have hb := (deferred_bounds hQ i).1 b x hx
  set T := (pt hQ i).ts + b
  have hT0 : Q.τ 0 ≤ T := by
    have := curTs_ge hQ (cstep hQ i); rw [← pt_ts] at this; omega
  obtain ⟨n, k, hc, hTk⟩ := pro_reached hQ hT0
  have hni : cstep hQ i < n := by
    by_contra h
    have := curTs_mono hQ (show n ≤ cstep hQ i by omega)
    simp only at this; rw [hc, ← pt_ts] at this; simp only [curTs] at this; omega
  have hΩ : (x, Deadline.ts T) ∈ (Q.run n).Ω :=
    obl_after hQ (Set.mem_biUnion hx (by simp [oblOf, T])) n hni
  obtain ⟨p, hp, hpr⟩ := pro_produces hc hTk ⟨_, Or.inr ⟨x, rfl, hΩ⟩⟩
  obtain ⟨hn, rfl⟩ := cstep_unique hQ hp
  set j := (Q.run n).len
  refine ⟨j, ⟨?_, ?_⟩, hpr.initTs k T hc ⟨x, rfl, hΩ⟩⟩
  · show (pt hQ j).ts = T; rw [hpr.ts, hc]; rfl
  · show T < (pt hQ (j + 1)).ts
    rw [pt_ts]
    exact curTs_after_pro hQ hc hTk _ (hn ▸ cstep_strictMono hQ (Nat.lt_succ_self j))

/-- **`next` obligations are discharged at the right time-point**, and a
    single `next` lands at most one time unit later. -/
theorem nextFire (hQ : Q.Wf v₀) (i n : ℕ) (t : Bool) (x : Ev B L × List D)
    (hx : Act.next n t x ∈ (pt hQ i).X) :
    (t = true → (outTr hQ).ts (i + 1) ≤ (outTr hQ).ts i + 1) ∧
      Act.cau x ∈ (pt hQ (i + n)).init := by
  obtain ⟨hn, htn⟩ := (deferred_bounds hQ i).2 n t x hx
  have hobl : (x, Deadline.tp (i + n)) ∈ newObl i (pt hQ i).ts (pt hQ i).X :=
    Set.mem_biUnion hx (by simp [oblOf])
  refine ⟨fun ht => ?_, ?_⟩
  · -- the obligation for time-point `i + 1` forces the next call to produce
    have hn1 := htn ht; subst hn1
    set ni := cstep hQ i
    have hlen1 : (Q.run (ni + 1)).len = i + 1 := by
      rw [(pt_spec hQ i).2.len, (cstep_spec hQ i).1]
    have hdue : (Q.dueTp (Q.run (ni + 1))).Nonempty :=
      ⟨_, x, rfl, by rw [hlen1]; exact obl_after hQ hobl _ (Nat.lt_succ_self _)⟩
    have hts_i : (pt hQ i).ts = Q.curTs (Q.run ni).cur := pt_ts hQ i
    -- the cursor after the call producing `i`
    have key : ∀ k t', (Q.run (ni + 1)).cur = .pro k t' → t' ≤ (pt hQ i).ts + 1 →
        Q.τ k ≤ t' → (outTr hQ).ts (i + 1) ≤ (outTr hQ).ts i + 1 := by
      intro k t' hc ht' hk
      show (pt hQ (i + 1)).ts ≤ (pt hQ i).ts + 1
      by_cases hlt : t' < Q.τ (k + 1)
      · obtain ⟨p, hp, hpr⟩ := pro_produces hc hlt (hdue.mono Set.subset_union_left)
        obtain ⟨-, rfl⟩ := cstep_unique hQ hp
        rw [hlen1] at hpr; rw [hpr.ts, hc]; exact ht'
      · have hc2 : (Q.run (ni + 2)).cur = .react (k + 1) := by
          rw [run_succ, step_next hc hlt]
        have hlen2 : (Q.run (ni + 2)).len = i + 1 := by
          rw [run_succ, step_next hc hlt]; exact hlen1
        obtain ⟨p, hp, hpr⟩ := react_produces hc2
        obtain ⟨-, rfl⟩ := cstep_unique hQ hp
        rw [hlen2] at hpr; rw [hpr.ts, hc2]
        have := (cur_inv hQ (ni + 1) k t' hc).2; simp only [curTs]; omega
    rcases hci : (Q.run ni).cur with k | ⟨k, t'⟩
    · have hc : (Q.run (ni + 1)).cur = .pro k (Q.τ k) := by rw [run_succ, step_react hci]
      exact key k _ hc (by rw [hts_i, hci]; simp [curTs]) le_rfl
    · have hlt : t' < Q.τ (k + 1) := by
        by_contra h
        have := (pt_spec hQ i).1
        simp only [prod] at this; rw [step_next hci h] at this; cases this
      have hc : (Q.run (ni + 1)).cur = .pro k (t' + 1) := by
        rw [run_succ]
        by_cases hC : (Q.dueTp (Q.run ni) ∪ Q.dueTs (Q.run ni) t').Nonempty
        · rw [step_pro_prod hci hlt hC]
        · rw [step_pro_none hci hlt hC]
      exact key k _ hc (by rw [hts_i, hci]; simp [curTs])
        (by have := (cur_inv hQ ni k t' hci).1; omega)
  · -- the time-point `i + n` is produced after the obligation was created
    have hlt : cstep hQ i < cstep hQ (i + n) := cstep_strictMono hQ (by omega)
    have hΩ := obl_after hQ hobl _ hlt
    exact (pt_spec hQ (i + n)).2.initTp ⟨x, rfl, by rw [(cstep_spec hQ (i + n)).1]; exact hΩ⟩

/-- The initial actions are due obligations of earlier time-points. -/
theorem initSrc (hQ : Q.Wf v₀) (j : ℕ) (a : Act B L D) (ha : a ∈ (pt hQ j).init) :
    ∃ x, a = Act.cau x ∧ ∃ i, (∃ b, Act.later b x ∈ (pt hQ i).X) ∨
      (∃ n t, Act.next n t x ∈ (pt hQ i).X) := by
  obtain ⟨x, rfl, dl, hdl⟩ := init_cau hQ j a ha
  obtain ⟨m, -, p, hp, ho⟩ := Ω_src _ _ hdl
  obtain ⟨-, rfl⟩ := cstep_unique hQ hp
  simp only [newObl, Set.mem_iUnion] at ho
  obtain ⟨b, hb, hob⟩ := ho
  refine ⟨x, rfl, (Q.run m).len, ?_⟩
  cases b with
  | later b' y => simp [oblOf] at hob; obtain ⟨rfl, -⟩ := hob; exact Or.inl ⟨b', hb⟩
  | next n t y => simp [oblOf] at hob; obtain ⟨rfl, -⟩ := hob; exact Or.inr ⟨n, t, hb⟩
  | cau y => simp [oblOf] at hob
  | sup y => simp [oblOf] at hob

/-- **The loop produces a `LoopRun`.** -/
noncomputable def loopRun (hQ : Q.Wf v₀) : LoopRun Q.P (outTr hQ) v₀ where
  K j := (pt hQ j).K
  D₀ j := (pt hQ j).D₀
  init j := (pt hQ j).init
  X j := (pt hQ j).X
  hv₀ j := by rw [(pt_spec hQ j).2.K]; exact hQ.hv₀ _ _
  run j := pt_satRun hQ j
  db _ := rfl
  lv _ := rfl
  laterFire := laterFire hQ
  nextFire := nextFire hQ
  initSrc := initSrc hQ

/-- The output timestamps are monotone. -/
theorem outTr_mono (hQ : Q.Wf v₀) : Monotone (outTr hQ).ts := pt_ts_mono hQ

/-! ## Finite traces: the loop is causal -/

/-- The call at this cursor only reads inputs `< N`. -/
def CurBefore (N : ℕ) : Cur → Prop
  | .react k => k < N
  | .pro k _ => k + 1 < N

/-- The same loop on another input trace. -/
def withInput (Q : LoopParams B L D) (τ' : ℕ → ℕ) (inDB' : ℕ → DB B L D) : LoopParams B L D :=
  { Q with τ := τ', inDB := inDB' }

theorem step_congr {τ' : ℕ → ℕ} {inDB' : ℕ → DB B L D} {N : ℕ}
    (hτ : ∀ k < N, Q.τ k = τ' k) (hdb : ∀ k < N, Q.inDB k = inDB' k)
    (s : LState B L D Q.TS) (hs : CurBefore N s.cur) :
    Q.step s = (withInput Q τ' inDB').step s := by
  rcases hc : s.cur with k | ⟨k, t⟩
  · rw [hc] at hs
    simp only [step, hc, withInput, hτ k hs, hdb k hs]; rfl
  · rw [hc] at hs
    simp only [step, hc, withInput, hτ (k + 1) hs]; rfl

/-- **Causality.**  Runs on two input traces agreeing on the first `N` inputs
    coincide as long as only these inputs are read. -/
theorem run_congr {τ' : ℕ → ℕ} {inDB' : ℕ → DB B L D} {N : ℕ}
    (hτ : ∀ k < N, Q.τ k = τ' k) (hdb : ∀ k < N, Q.inDB k = inDB' k) :
    ∀ n, (∀ m < n, CurBefore N (Q.run m).cur) →
      Q.run n = (withInput Q τ' inDB').run n ∧ ∀ m < n, Q.prod m = (withInput Q τ' inDB').prod m
  | 0, _ => ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, h => by
    obtain ⟨ih, ihp⟩ := run_congr hτ hdb n fun m hm => h m (by omega)
    have hst := step_congr hτ hdb (Q.run n) (h n (by omega))
    refine ⟨?_, fun m hm => ?_⟩
    · show (Q.step (Q.run n)).1 = ((withInput Q τ' inDB').step ((withInput Q τ' inDB').run n)).1
      rw [hst]; exact congrArg _ (congrArg _ ih)
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hm | rfl
      · exact ihp m hm
      · show (Q.step (Q.run m)).2 = ((withInput Q τ' inDB').step ((withInput Q τ' inDB').run m)).2
        rw [hst, ← ih]

/-- **Finite traces.**  If two well-formed input traces agree on the first
    `N` inputs, the output time-points produced while only reading these
    inputs coincide: the enforced output of a finite trace is a prefix of the
    enforced output of any of its infinite extensions (e.g. with empty
    inputs, which is what the engine's final flush of obligations does). -/
theorem pt_congr {v₀ : ℕ → D} {τ' : ℕ → ℕ} {inDB' : ℕ → DB B L D} {N : ℕ}
    (hQ : Q.Wf v₀) (hQ' : (withInput Q τ' inDB').Wf v₀)
    (hτ : ∀ k < N, Q.τ k = τ' k) (hdb : ∀ k < N, Q.inDB k = inDB' k)
    (j : ℕ) (hj : ∀ m ≤ cstep hQ j, CurBefore N (Q.run m).cur) :
    pt hQ j = pt hQ' j ∧ (outTr hQ).ts j = (outTr hQ').ts j ∧ (outTr hQ).db j = (outTr hQ').db j := by
  obtain ⟨hrun, hprod⟩ := run_congr hτ hdb (cstep hQ j + 1) fun m hm => hj m (by omega)
  have hp := (pt_spec hQ j).1
  rw [hprod _ (Nat.lt_succ_self _)] at hp
  obtain ⟨hn, hpt⟩ := cstep_unique hQ' hp
  have hlen : ((withInput Q τ' inDB').run (cstep hQ j)).len = j := by
    rw [← (run_congr hτ hdb (cstep hQ j) fun m hm => hj m (by omega)).1]; exact (cstep_spec hQ j).1
  rw [hlen] at hpt
  exact ⟨hpt, by simp [outTr, hpt], by simp [outTr, hpt]⟩

/-- The reactive time-point for input `N - 1` and everything before it only
    read the first `N` inputs. -/
theorem before_react {N n : ℕ} (hn : (Q.run n).cur = .react (N - 1)) (hN : 0 < N) :
    ∀ m ≤ n, CurBefore N (Q.run m).cur := by
  intro m hm
  -- the cursor's block index is monotone
  have blk : ∀ a b, a ≤ b → ∀ k k', ((Q.run a).cur = .react k ∨ ∃ t, (Q.run a).cur = .pro k t) →
      ((Q.run b).cur = .react k' ∨ ∃ t, (Q.run b).cur = .pro k' t) →
      k ≤ k' ∧ ((Q.run a).cur = .react k → True) := by
    intro a b hab
    induction hab with
    | refl =>
      intro k k' h1 h2
      rcases h1 with h1 | ⟨t, h1⟩ <;> rcases h2 with h2 | ⟨t', h2⟩ <;> rw [h1] at h2 <;> cases h2 <;>
        exact ⟨le_rfl, fun _ => trivial⟩
    | @step b hb ih =>
      intro k k' h1 h2
      -- the cursor at `b`
      rcases hcb : (Q.run b).cur with k'' | ⟨k'', t''⟩
      · obtain ⟨hk, -⟩ := ih k k'' h1 (Or.inl hcb)
        rw [run_succ, step_react hcb] at h2
        rcases h2 with h2 | ⟨t, h2⟩ <;> cases h2
        exact ⟨hk, fun _ => trivial⟩
      · obtain ⟨hk, -⟩ := ih k k'' h1 (Or.inr ⟨t'', hcb⟩)
        rw [run_succ] at h2
        by_cases ht : t'' < Q.τ (k'' + 1)
        · by_cases hC : (Q.dueTp (Q.run b) ∪ Q.dueTs (Q.run b) t'').Nonempty
          · rw [step_pro_prod hcb ht hC] at h2
            rcases h2 with h2 | ⟨t, h2⟩ <;> cases h2; exact ⟨hk, fun _ => trivial⟩
          · rw [step_pro_none hcb ht hC] at h2
            rcases h2 with h2 | ⟨t, h2⟩ <;> cases h2; exact ⟨hk, fun _ => trivial⟩
        · rw [step_next hcb ht] at h2
          rcases h2 with h2 | ⟨t, h2⟩ <;> cases h2; exact ⟨by omega, fun _ => trivial⟩
  have hcur : ∀ c : Cur, ∃ k, (c = .react k ∨ ∃ t, c = .pro k t) := fun c => by
    cases c with
    | react k => exact ⟨k, Or.inl rfl⟩
    | pro k t => exact ⟨k, Or.inr ⟨t, rfl⟩⟩
  obtain ⟨k, hk⟩ := hcur (Q.run m).cur
  have hle := (blk m n hm k (N - 1) hk (Or.inl hn)).1
  rcases hk with hk | ⟨t, hk⟩
  · rw [hk]; show k < N; omega
  · rw [hk]; show k + 1 < N
    -- a proactive cursor of block `N - 1` cannot precede the reactive call of `N - 1`
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · omega
    · exfalso
      subst heq
      -- after `pro (N-1) t`, the cursor never returns to `react (N-1)`
      have : ∀ b, m ≤ b → (Q.run b).cur ≠ .react (N - 1) := by
        intro b hb
        induction hb with
        | refl => rw [hk]; exact fun h => by cases h
        | @step b hb ih =>
          intro h
          rcases hcb : (Q.run b).cur with k'' | ⟨k'', t''⟩
          · rw [run_succ, step_react hcb] at h; cases h
          · have hk'' := (blk m b hb (N - 1) k'' (Or.inr ⟨t, hk⟩) (Or.inr ⟨t'', hcb⟩)).1
            rw [run_succ] at h
            by_cases ht : t'' < Q.τ (k'' + 1)
            · by_cases hC : (Q.dueTp (Q.run b) ∪ Q.dueTs (Q.run b) t'').Nonempty
              · rw [step_pro_prod hcb ht hC] at h; cases h
              · rw [step_pro_none hcb ht hC] at h; cases h
            · rw [step_next hcb ht] at h
              have := Cur.react.inj h; omega
      exact this n hm hn

end LoopParams

end Enfflash
