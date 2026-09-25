/-
  Enfflash formalization — a concrete implementation of EF tables and lets
  inside the enforcement loop (paper, Algorithm 2: `Interp`, `Eval`, and the
  table updates of `Saturate`).

  The table state holds, for every `since` let, its stored rows `(τ', ā)`,
  and for every `prev` let, the rows of the previous time-point (a lagged
  table).  On a working set `W`, lets are evaluated in let order: a present
  let evaluates its body, a since let reads its stored rows (minus those whose
  left operand fails now) plus the new rows (whose right operand holds now),
  and a prev let reads its lagged rows; all within the window `[a, b]`.
  After a time-point, the rows are committed.

  `tables_compute`: in the loop's output, these tables compute exactly the
  MFOTL meaning of the lets (`TablesComputeLets`, hence `LetSem`).
-/
import Enfflash.Loop
import Enfflash.Tables
import Enfflash.LetNormal

namespace Enfflash

variable {B D : Type}

/-- The table state. -/
structure Tab (D : Type) where
  since : ℕ → Set (ℕ × List D)
  lag : ℕ → Set (ℕ × List D)

section
variable (Γ : List (LetDef B ℕ D)) (v₀ : ℕ → D)

/-- Evaluate a present formula on the working set. -/
def sat0 (W : DB B ℕ D) (lv : ℕ → List D → Prop) (φ : Fm B ℕ D) (as : List D) : Prop :=
  (ptTr W lv).sat 0 (vapp as v₀) φ

/-- The value of let `p` with body `body`, given the values of earlier lets. -/
def bodyVal (tab : Tab D) (t : ℕ) (W : DB B ℕ D) (lv : ℕ → List D → Prop) (p : ℕ) :
    LBody B ℕ D → List D → Prop
  | .now φ, as => sat0 v₀ W lv φ as
  | .since a b φl φr, as => ∃ τ', ((τ', as) ∈ tab.since p ∧ sat0 v₀ W lv φl as ∨
      τ' = t ∧ sat0 v₀ W lv φr as) ∧ inI a b (t - τ')
  | .prev a b _, as => ∃ τ', (τ', as) ∈ tab.lag p ∧ inI a b (t - τ')
  | .agg k ω ts ys φ, as =>
    aggSem k ω ts ys (vapp as v₀) (fun ds => (ptTr W lv).sat 0 (vapp ds (vapp as v₀)) φ)

/-- Values of the lets `< n`. -/
def lvUpTo (tab : Tab D) (t : ℕ) (W : DB B ℕ D) : ℕ → ℕ → List D → Prop
  | 0 => fun _ _ => False
  | n + 1 => fun q as => if q < n then lvUpTo tab t W n q as else if q = n then
      (match Γ[n]? with
       | some d => as.length = d.arity ∧ bodyVal v₀ tab t W (lvUpTo tab t W n) n d.body as
       | none => False)
      else False

/-- The let interpretation on a working set. -/
def lvOf (tab : Tab D) (t : ℕ) (W : DB B ℕ D) (q : ℕ) : List D → Prop :=
  lvUpTo Γ v₀ tab t W (q + 1) q

/-- Commit the tables after a time-point with timestamp `t` and final
    working set `W`. -/
def commitTab (tab : Tab D) (t : ℕ) (W : DB B ℕ D) : Tab D where
  since n := match Γ[n]? with
    | some ⟨ar, .since _ _ φl φr⟩ =>
      {r | r ∈ tab.since n ∧ sat0 v₀ W (lvOf Γ v₀ tab t W) φl r.2} ∪
      {r | r.1 = t ∧ r.2.length = ar ∧ sat0 v₀ W (lvOf Γ v₀ tab t W) φr r.2}
    | _ => ∅
  lag n := match Γ[n]? with
    | some ⟨ar, .prev _ _ φ⟩ =>
      {r | r.1 = t ∧ r.2.length = ar ∧ sat0 v₀ W (lvOf Γ v₀ tab t W) φ r.2}
    | _ => ∅

/-- Reachable table states: finitely many finite stores. -/
def TabInv (tab : Tab D) : Prop :=
  ∀ n, (tab.since n).Finite ∧ (tab.lag n).Finite ∧
    (Γ.length ≤ n → tab.since n = ∅ ∧ tab.lag n = ∅)

/-- The loop with concrete tables. -/
def tableParams (τ : ℕ → ℕ) (inDB : ℕ → DB B ℕ D) (P : Program B ℕ D)
    (Sat : Ctx B ℕ D → DB B ℕ D → Set (Act B ℕ D) → Set (Act B ℕ D)) : LoopParams B ℕ D where
  τ := τ
  inDB := inDB
  P := P
  TS := Tab D
  tab₀ := ⟨fun _ => ∅, fun _ => ∅⟩
  inv := TabInv Γ
  ctx tab t := ⟨fun W => lvOf Γ v₀ tab t W, v₀⟩
  commit := commitTab Γ v₀
  Sat := Sat

end

/-! ## Let evaluation follows the let order -/

theorem lvUpTo_stable (Γ : List (LetDef B ℕ D)) (v₀ : ℕ → D) (tab : Tab D) (t : ℕ)
    (W : DB B ℕ D) : ∀ m q, q < m → lvUpTo Γ v₀ tab t W m q = lvOf Γ v₀ tab t W q
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, q, h => by
    funext as
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | rfl
    · simp only [lvUpTo, h', if_true]; rw [lvUpTo_stable Γ v₀ tab t W n q h']
    · rfl

theorem Tr.sat_congr_lets {L : Type} {σ σ' : Tr B L D} (hdb : σ.db = σ'.db) (hts : σ.ts = σ'.ts)
    (φ : Fm B L D) (hlv : ∀ i, ∀ p ∈ φ.lets, σ.lv i p = σ'.lv i p) :
    ∀ i v, σ.sat i v φ ↔ σ'.sat i v φ := by
  induction φ with
  | tt | eq => intros; rfl
  | pred p ts =>
    intro i v
    cases p with
    | ev e => simp [Tr.sat, Tr.prIn, hdb]
    | lp p => simp only [Tr.sat, Tr.prIn]; rw [hlv i p (by simp [Fm.lets])]
  | neg φ ih => intro i v; simp only [Tr.sat]; rw [ih hlv]
  | ex φ ih => intro i v; simp only [Tr.sat]; exact exists_congr fun d => ih hlv i _
  | conj φ ψ ih₁ ih₂ =>
    intro i v; simp only [Tr.sat]
    rw [ih₁ fun i p hp => hlv i p (by simp [Fm.lets, hp]), ih₂ fun i p hp => hlv i p (by simp [Fm.lets, hp])]
  | ev a b φ ih =>
    intro i v; simp only [Tr.sat, hts]
    exact exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => ih hlv j v
  | nx a b φ ih => intro i v; simp only [Tr.sat, hts]; rw [ih hlv]

/-- The fixpoint equation of let evaluation, for ordered lets. -/
theorem lvOf_eq (Γ : List (LetDef B ℕ D)) (v₀ : ℕ → D)
    (hord : ∀ (p : ℕ) (d : LetDef B ℕ D), Γ[p]? = some d → ∀ q ∈ d.body.lets, q < p)
    (tab : Tab D) (t : ℕ) (W : DB B ℕ D) {p : ℕ} {d : LetDef B ℕ D} (hd : Γ[p]? = some d)
    (as : List D) :
    lvOf Γ v₀ tab t W p as ↔
      as.length = d.arity ∧ bodyVal v₀ tab t W (lvOf Γ v₀ tab t W) p d.body as := by
  have hunf : lvOf Γ v₀ tab t W p as ↔
      as.length = d.arity ∧ bodyVal v₀ tab t W (lvUpTo Γ v₀ tab t W p) p d.body as := by
    simp [lvOf, lvUpTo, hd]
  rw [hunf]
  refine and_congr_right fun _ => ?_
  have hlow : ∀ q ∈ d.body.lets, lvUpTo Γ v₀ tab t W p q = lvOf Γ v₀ tab t W q :=
    fun q hq => lvUpTo_stable Γ v₀ tab t W p q (hord p d hd q hq)
  have hsat : ∀ φ : Fm B ℕ D, (∀ q ∈ φ.lets, q ∈ d.body.lets) → ∀ as,
      sat0 v₀ W (lvUpTo Γ v₀ tab t W p) φ as ↔ sat0 v₀ W (lvOf Γ v₀ tab t W) φ as :=
    fun φ hφ as => Tr.sat_congr_lets (σ := ptTr W (lvUpTo Γ v₀ tab t W p))
      (σ' := ptTr W (lvOf Γ v₀ tab t W)) rfl rfl φ (fun _ q hq => hlow q (hφ q hq)) 0 _
  cases hb : d.body with
  | now φ => exact hsat φ (by simp [hb, LBody.lets]) as
  | since a b φl φr =>
    simp only [bodyVal]
    rw [hsat φl (by simp [hb, LBody.lets]; tauto) as, hsat φr (by simp [hb, LBody.lets]; tauto) as]
  | prev => rfl
  | agg k ω ts ys φ =>
    simp only [bodyVal]
    exact aggSem_congr (fun ds _ => Tr.sat_congr_lets (σ := ptTr W (lvUpTo Γ v₀ tab t W p))
      (σ' := ptTr W (lvOf Γ v₀ tab t W)) rfl rfl φ
      (fun _ q hq => hlow q (by simp [hb, LBody.lets, hq])) 0 _) (fun _ _ => rfl) rfl

/-! ## Tables in the loop -/

section
variable {Γ : List (LetDef B ℕ D)} {v₀ : ℕ → D} {τ : ℕ → ℕ} {inDB : ℕ → DB B ℕ D}
  {P : Program B ℕ D} {Sat : Ctx B ℕ D → DB B ℕ D → Set (Act B ℕ D) → Set (Act B ℕ D)}

local notation "QQ" => tableParams Γ v₀ τ inDB P Sat

open LoopParams

/-- The table state before time-point `j`. -/
noncomputable def tabAt (hQ : (QQ).Wf v₀) (j : ℕ) : Tab D := ((QQ).run (cstep hQ j)).tab

theorem no_prod_between (hQ : (QQ).Wf v₀) {j n : ℕ} (h1 : cstep hQ j < n)
    (h2 : n < cstep hQ (j + 1)) : (QQ).prod n = none := by
  rcases hp : (QQ).prod n with _ | p
  · rfl
  obtain ⟨hn, -⟩ := cstep_unique hQ hp
  have l1 := len_mono (Q := QQ) (show cstep hQ j + 1 ≤ n by omega)
  have l2 := len_mono (Q := QQ) (show n ≤ cstep hQ (j + 1) by omega)
  simp only [(cstep_spec hQ (j + 1)).1] at l2
  simp only [(pt_spec hQ j).2.len, (cstep_spec hQ j).1] at l1
  have : ((QQ).run n).len = j + 1 := by omega
  rw [this] at hn; omega

theorem no_prod_before (hQ : (QQ).Wf v₀) {n : ℕ} (h : n < cstep hQ 0) : (QQ).prod n = none := by
  rcases hp : (QQ).prod n with _ | p
  · rfl
  obtain ⟨hn, -⟩ := cstep_unique hQ hp
  have := len_mono (Q := QQ) (show n + 1 ≤ cstep hQ 0 by omega)
  simp only [(cstep_spec hQ 0).1] at this
  rcases prod_cases (Q := QQ) n with ⟨h', -⟩ | ⟨p', -, hpr⟩
  · rw [hp] at h'; cases h'
  · rw [hpr.len] at this; omega

theorem tab_const {a b : ℕ} (hab : a ≤ b)
    (h : ∀ n, a ≤ n → n < b → (QQ).prod n = none) : ((QQ).run b).tab = ((QQ).run a).tab := by
  induction hab with
  | refl => rfl
  | @step m hm ih =>
    rw [← ih (fun n h1 h2 => h n h1 (by omega))]
    rcases prod_cases (Q := QQ) m with ⟨-, -, -, ht⟩ | ⟨p, hp, -⟩
    · exact ht
    · rw [h m hm (by omega)] at hp; cases hp

theorem tabAt_zero (hQ : (QQ).Wf v₀) : tabAt hQ 0 = ⟨fun _ => ∅, fun _ => ∅⟩ :=
  tab_const (Nat.zero_le _) fun _ _ h => no_prod_before hQ h

theorem tabAt_succ (hQ : (QQ).Wf v₀) (j : ℕ) :
    tabAt hQ (j + 1) = commitTab Γ v₀ (tabAt hQ j) (pt hQ j).ts
      (work (pt hQ j).D₀ (pt hQ j).X) := by
  unfold tabAt
  rw [tab_const (a := cstep hQ j + 1) (cstep_strictMono hQ (Nat.lt_succ_self j))
    fun n h1 h2 => no_prod_between hQ (by omega) h2]
  exact (pt_spec hQ j).2.tab

theorem sat0_iff (hQ : (QQ).Wf v₀) (j : ℕ) {φ : Fm B ℕ D} (hφ : φ.present) (as : List D) :
    sat0 v₀ (work (pt hQ j).D₀ (pt hQ j).X)
        (lvOf Γ v₀ (tabAt hQ j) (pt hQ j).ts (work (pt hQ j).D₀ (pt hQ j).X)) φ as ↔
      (outTr hQ).sat j (vapp as v₀) φ := by
  unfold sat0
  refine (Tr.sat_present (outTr hQ) _ j 0 rfl ?_ φ hφ _).symm
  simp only [outTr, ptTr, (pt_spec hQ j).2.K, tabAt]; rfl

theorem satW_iff (hQ : (QQ).Wf v₀) (j : ℕ) {φ : Fm B ℕ D} (hφ : φ.present) (w : ℕ → D) :
    (ptTr (work (pt hQ j).D₀ (pt hQ j).X)
        (lvOf Γ v₀ (tabAt hQ j) (pt hQ j).ts (work (pt hQ j).D₀ (pt hQ j).X))).sat 0 w φ ↔
      (outTr hQ).sat j w φ := by
  refine (Tr.sat_present (outTr hQ) _ j 0 rfl ?_ φ hφ w).symm
  simp only [outTr, ptTr, (pt_spec hQ j).2.K, tabAt]; rfl

/-- The stored rows are the since store and the previous time-point's rows
    (restricted to the let's arity). -/
theorem tabAt_spec (hQ : (QQ).Wf v₀)
    (hpres : ∀ (p : ℕ) (d : LetDef B ℕ D), Γ[p]? = some d → d.body.presentOps) :
    ∀ j, (∀ p ar a b φl φr, Γ[p]? = some ⟨ar, .since a b φl φr⟩ →
        (tabAt hQ (j + 1)).since p = {r | r ∈ sinceStore (outTr hQ) v₀ φl φr j ∧ r.2.length = ar}) ∧
      (∀ p ar a b φ, Γ[p]? = some ⟨ar, .prev a b φ⟩ →
        (tabAt hQ (j + 1)).lag p =
          {r | r.1 = (outTr hQ).ts j ∧ r.2.length = ar ∧ (outTr hQ).sat j (vapp r.2 v₀) φ}) := by
  intro j
  induction j with
  | zero =>
    refine ⟨fun p ar a b φl φr hd => ?_, fun p ar a b φ hd => ?_⟩
    · have hp := hpres p _ hd
      rw [tabAt_succ]
      ext r
      simp only [commitTab, hd, sinceStore, Set.mem_union, Set.mem_setOf_eq]
      rw [sat0_iff hQ 0 hp.1, sat0_iff hQ 0 hp.2, tabAt_zero]
      simp only [Set.mem_empty_iff_false, false_and, false_or]
      show _ ↔ (r.1 = (pt hQ 0).ts ∧ _) ∧ _
      tauto
    · have hp := hpres p _ hd
      rw [tabAt_succ]
      ext r
      simp only [commitTab, hd, Set.mem_setOf_eq]
      rw [sat0_iff hQ 0 hp]; rfl
  | succ j ih =>
    refine ⟨fun p ar a b φl φr hd => ?_, fun p ar a b φ hd => ?_⟩
    · have hp := hpres p _ hd
      rw [tabAt_succ]
      ext r
      simp only [commitTab, hd, sinceStore, Set.mem_union, Set.mem_setOf_eq]
      rw [ih.1 p ar a b φl φr hd, sat0_iff hQ (j + 1) hp.1, sat0_iff hQ (j + 1) hp.2]
      simp only [Set.mem_setOf_eq]
      show _ ↔ (_ ∨ r.1 = (pt hQ (j + 1)).ts ∧ _) ∧ _
      tauto
    · have hp := hpres p _ hd
      rw [tabAt_succ]
      ext r
      simp only [commitTab, hd, Set.mem_setOf_eq]
      rw [sat0_iff hQ (j + 1) hp]; rfl

/-- **The concrete tables compute the lets.** -/
theorem tables_compute (hQ : (QQ).Wf v₀)
    (hord : ∀ (p : ℕ) (d : LetDef B ℕ D), Γ[p]? = some d → ∀ q ∈ d.body.lets, q < p)
    (hpres : ∀ (p : ℕ) (d : LetDef B ℕ D), Γ[p]? = some d → d.body.presentOps) :
    TablesComputeLets (outTr hQ) v₀ (envOf Γ) := by
  intro p d hd i as hlen
  have hlv : (outTr hQ).lv i p as ↔
      bodyVal v₀ (tabAt hQ i) (pt hQ i).ts (work (pt hQ i).D₀ (pt hQ i).X)
        (lvOf Γ v₀ (tabAt hQ i) (pt hQ i).ts (work (pt hQ i).D₀ (pt hQ i).X)) p d.body as := by
    have := lvOf_eq Γ v₀ hord (tabAt hQ i) (pt hQ i).ts (work (pt hQ i).D₀ (pt hQ i).X) hd as
    rw [and_iff_right hlen] at this
    rw [← this]
    simp only [outTr, (pt_spec hQ i).2.K, tabAt]; rfl
  have hp := hpres p d hd
  rcases hb : d.body with φ | ⟨a, b, φl, φr⟩ | ⟨a, b, φ⟩ | ⟨k, ω, ts, ys, φ⟩
  · rw [hb] at hlv hp; simp only [bodyVal] at hlv
    exact hlv.trans (sat0_iff hQ i hp as)
  · rw [hb] at hlv hp
    simp only [bodyVal] at hlv
    rw [hlv, sat0_iff hQ i hp.1, sat0_iff hQ i hp.2]
    simp only [sinceVal]
    cases i with
    | zero =>
      rw [tabAt_zero]
      simp [sinceStore]
    | succ j =>
      rw [(tabAt_spec hQ hpres j).1 p d.arity a b φl φr
        (by rw [show Γ[p]? = some d from hd, ← hb])]
      simp only [sinceStore, Set.mem_union, Set.mem_setOf_eq, hlen, and_true]
      constructor
      · rintro ⟨τ', h | ⟨rfl, h⟩, hI⟩
        exacts [⟨τ', Or.inl h, hI⟩, ⟨_, Or.inr ⟨rfl, h⟩, hI⟩]
      · rintro ⟨τ', h | ⟨h1, h⟩, hI⟩
        exacts [⟨τ', Or.inl h, hI⟩, ⟨τ', Or.inr ⟨h1, h⟩, hI⟩]
  · rw [hb] at hlv
    simp only [bodyVal] at hlv
    rw [hlv]
    cases i with
    | zero => rw [tabAt_zero]; simp [prevVal]
    | succ j =>
      rw [(tabAt_spec hQ hpres j).2 p d.arity a b φ
        (by rw [show Γ[p]? = some d from hd, ← hb])]
      simp only [prevVal, Set.mem_setOf_eq, hlen, true_and]
      constructor
      · rintro ⟨τ', ⟨rfl, h⟩, hI⟩; exact ⟨_, ⟨rfl, h⟩, hI⟩
      · rintro ⟨τ', ⟨rfl, h⟩, hI⟩; exact ⟨_, ⟨rfl, h⟩, hI⟩
  · rw [hb] at hlv hp
    simp only [bodyVal] at hlv
    rw [hlv]
    exact aggSem_congr (fun ds _ => satW_iff hQ i hp _) (fun _ _ => rfl) rfl

end

end Enfflash
