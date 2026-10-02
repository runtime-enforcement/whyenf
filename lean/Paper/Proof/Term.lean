/-
  Termination of `Saturate` (the DFG check of §4.5).
-/
import Paper.Proof.Prod

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem lists_finite {W : Set Voc.𝔻} (hW : W.Finite) :
    ∀ n, {l : List Voc.𝔻 | l.length = n ∧ ∀ x ∈ l, x ∈ W}.Finite
  | 0 => (Set.finite_singleton []).subset fun l hl => by
      simp only [Set.mem_setOf_eq, List.length_eq_zero_iff] at hl; simp [hl.1]
  | n + 1 => by
    refine ((hW.prod (lists_finite hW n)).image fun p => p.1 :: p.2).subset ?_
    rintro l ⟨hl, hx⟩
    cases l with
    | nil => simp at hl
    | cons a l =>
      exact ⟨(a, l), ⟨hx a (by simp), by simpa using hl, fun x hx' => hx x (by simp [hx'])⟩, rfl⟩

namespace Setup
variable {U : Setup Voc}

namespace TIn
variable (I : U.TIn)

/-- The finite bound on all values. -/
def Wst : Set Voc.𝔻 := Wb U.O I.B U.Φ U.Lmax

theorem Wst_finite : I.Wst.Finite :=
  Wb_finite U.O I.B U.Φ I.B_finite (fun _ hX => U.Φ_finite hX) _

theorem WB_Wst (q : Pos Voc) : I.WB q ⊆ I.Wst := Wb_mono U.O I.B U.Φ (U.Lv_le q)

/-- The possible events. -/
def UE : Set (REv Voc) := {e | e.2.length = Voc.ι e.1 ∧ ∀ x ∈ e.2, x ∈ I.Wst}

theorem UE_finite : I.UE.Finite := by
  haveI := U.toFinalSetting.Ξ.cauN |> fun _ => (Voc.finE)
  refine (Set.finite_univ.biUnion (t := fun e : Voc.ℰ =>
      (fun l => (e, l)) '' {l | l.length = Voc.ι e ∧ ∀ x ∈ l, x ∈ I.Wst})
    fun e _ => (lists_finite I.Wst_finite _).image _).subset ?_
  rintro ⟨e, l⟩ ⟨hl, hx⟩
  exact Set.mem_biUnion (Set.mem_univ e) ⟨l, ⟨hl, hx⟩, rfl⟩

/-- The possible deadlines, for `|σ| = len`. -/
def Dl (len : ℕ) : Set (DKind × ℕ) :=
  {d | ∃ c ∈ U.R, (∃ n e ts, c.ε = .ev (Interval.icc n n le_rfl) e ts ∧ d = (.ts, I.τ + n)) ∨
    (∃ n e ts, c.ε = .nexts n e ts ∧ d = (.tp, len + n))}

theorem Dl_finite (len : ℕ) : (I.Dl len).Finite := by
  refine (U.R_finite.biUnion fun c _ => (Set.Subsingleton.finite (s := {d : DKind × ℕ |
      ∃ n e ts, c.ε = .ev (Interval.icc n n le_rfl) e ts ∧ d = (.ts, I.τ + n)}) ?_).union
    (Set.Subsingleton.finite (s := {d : DKind × ℕ | ∃ n e ts, c.ε = .nexts n e ts ∧
      d = (.tp, len + n)}) ?_)).subset ?_
  · rintro d ⟨n, e, ts, h1, rfl⟩ d' ⟨n', e', ts', h1', rfl⟩
    rw [h1] at h1'; simp only [Effect.ev.injEq] at h1'
    rw [icc_inj h1'.1]
  · rintro d ⟨n, e, ts, h1, rfl⟩ d' ⟨n', e', ts', h1', rfl⟩
    rw [h1] at h1'; simp only [Effect.nexts.injEq] at h1'; rw [h1'.1]
  · rintro d ⟨c, hc, h⟩; exact Set.mem_biUnion hc h

/-- The invariant of the states of one time-point. -/
structure Inv (Ω₀ : Set (Obligation Voc)) (len : ℕ) (y : Trip Voc) : Prop where
  goodC : U.Good y.2.1
  goodS : U.Good y.2.2
  vb : I.VB y
  om : ∀ o ∈ y.1, o ∈ Ω₀ ∨ (o.1 ∈ I.UE ∧ o.2 ∈ I.Dl len)

theorem Inv.init (Ω₀ : Set (Obligation Voc)) (len : ℕ) : I.Inv Ω₀ len (Ω₀, I.C₀, ∅) := by
  refine ⟨I.hC₀, fun e he => absurd he (Set.notMem_empty _), ?_, fun o ho => Or.inl ho⟩
  rintro e (he | he) k hk
  · exact I.B_WB _ (Or.inl (Or.inl (Or.inl ⟨e, Or.inr he, List.getElem_mem hk⟩)))
  · exact absurd he (Set.notMem_empty _)

theorem Inv.step {Ω₀ : Set (Obligation Voc)} (σ : Trace Voc.toSignature) {y : Trip Voc}
    (h : I.Inv Ω₀ (Trace.len σ) y) {c : EClause Voc} (hc : c ∈ U.R) :
    I.Inv Ω₀ (Trace.len σ) (y.union (I.toPtIn.Δ (Trace.len σ) c y)) := by
  obtain ⟨d1, d2, d3, d4⟩ := I.toPtIn.Δ_good σ hc y
  have hA : ∀ a ∈ I.toPtIn.A c y, ∀ k (hk : k < a.length), a[k] ∈ I.WB (c.ε.name, k) := by
    rintro a ⟨v, hv, hva⟩ k hk
    exact I.rule_bound h.goodC h.vb hc hv hva k hk
  refine ⟨fun e he => ?_, fun e he => ?_, ?_, fun o ho => ?_⟩
  · rcases he with he | he
    · exact h.goodC e he
    · exact d1 e he
  · rcases he with he | he
    · exact h.goodS e he
    · exact d2 e he
  · rintro e ((he | he) | (he | he)) k hk
    · exact h.vb e (Or.inl he) k hk
    · have hn := d3 e he
      simp only [PtIn.Δ] at he
      cases hε : c.ε <;> rw [hε] at he <;> simp at he
      obtain ⟨-, ha⟩ := he
      rw [hn]; exact hA _ ha k hk
    · exact h.vb e (Or.inr he) k hk
    · have hn := d4 e he
      simp only [PtIn.Δ] at he
      cases hε : c.ε <;> rw [hε] at he <;> simp at he
      obtain ⟨-, ha⟩ := he
      rw [hn]; exact hA _ ha k hk
  · rcases ho with ho | ho
    · exact h.om o ho
    · right
      obtain ⟨⟨hlen, -⟩, -⟩ := U.R_props c hc
      simp only [PtIn.Δ] at ho
      cases hε : c.ε with
      | cau | sup => rw [hε] at ho; simp at ho
      | ev J e ts =>
        rw [hε] at ho
        obtain ⟨n, hJ, h1, h2, h3⟩ := ho
        subst hJ
        refine ⟨⟨?_, fun x hx => ?_⟩, ⟨c, hc, Or.inl ⟨n, e, ts, hε, h3⟩⟩⟩
        · obtain ⟨v, -, hva⟩ := h2; rw [h1, evalList_length hva, hlen, hε]; rfl
        · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
          exact I.WB_Wst _ (hA _ h2 k hk)
      | nexts n e ts =>
        rw [hε] at ho
        obtain ⟨h1, h2, h3⟩ := ho
        refine ⟨⟨?_, fun x hx => ?_⟩, ⟨c, hc, Or.inr ⟨n, e, ts, hε, h3⟩⟩⟩
        · obtain ⟨v, -, hva⟩ := h2; rw [h1, evalList_length hva, hlen, hε]; rfl
        · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
          exact I.WB_Wst _ (hA _ h2 k hk)

/-- The finite set of possible states. -/
def F (Ω₀ : Set (Obligation Voc)) (len : ℕ) : Set (Trip Voc) :=
  {s : Set (Obligation Voc) | s ⊆ Ω₀ ∪ {o | o.1 ∈ I.UE ∧ o.2 ∈ I.Dl len}} ×ˢ
    ({s : Set (REv Voc) | s ⊆ I.UE} ×ˢ {s : Set (REv Voc) | s ⊆ I.UE})

theorem F_finite {Ω₀ : Set (Obligation Voc)} (hΩ : Ω₀.Finite) (len : ℕ) : (I.F Ω₀ len).Finite := by
  refine Set.Finite.prod ?_ (Set.Finite.prod I.UE_finite.finite_subsets I.UE_finite.finite_subsets)
  refine (hΩ.union ?_).finite_subsets
  exact ((I.UE_finite.prod (I.Dl_finite len)).subset fun o ⟨h1, h2⟩ => ⟨h1, h2⟩)

theorem Inv.mem_F {Ω₀ : Set (Obligation Voc)} {len : ℕ} {y : Trip Voc} (h : I.Inv Ω₀ len y) :
    y ∈ I.F Ω₀ len := by
  refine ⟨fun o ho => h.om o ho, fun e he => ⟨(h.goodC e he).1, fun x hx => ?_⟩,
    fun e he => ⟨(h.goodS e he).1, fun x hx => ?_⟩⟩
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact I.WB_Wst _ (h.vb e (Or.inl he) k hk)
  · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
    exact I.WB_Wst _ (h.vb e (Or.inr he) k hk)

theorem Inv.reach {Ω₀ : Set (Obligation Voc)} (σ : Trace Voc.toSignature)
    {g : List (EClause Voc × Item Voc)} {r : ℕ} (hg : ∀ p ∈ g, U.SecRule r p) {x y : Trip Voc}
    (hr : ReachS U.P (TablesOf U.L.lets I.H) I.τ I.D σ (g.map Prod.snd) x y)
    (hx : I.Inv Ω₀ (Trace.len σ) x) : I.Inv Ω₀ (Trace.len σ) y := by
  induction hr with
  | refl => exact hx
  | step it hit _ ih =>
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hit
    rw [I.toPtIn.upd_rule (hg p hp).spec σ ih.goodC]
    exact ih.step I σ (hg p hp).mem

theorem section_some {Ω₀ : Set (Obligation Voc)} (hΩ : Ω₀.Finite) (σ : Trace Voc.toSignature)
    {g : List (EClause Voc × Item Voc)} {r : ℕ} (hg : ∀ p ∈ g, U.SecRule r p) {x : Trip Voc}
    (hx : I.Inv Ω₀ (Trace.len σ) x) :
    (repeatUntilUnchanged (pass U.P (g.map Prod.snd) (TablesOf U.L.lets I.H) I.τ I.D σ) x).isSome := by
  refine repeat_isSome (pass_infl _ _ _ _ _ _) (I.F Ω₀ (Trace.len σ)) (I.F_finite hΩ _) fun k => ?_
  refine (hx.reach I σ hg ?_).mem_F
  induction k with
  | zero => exact .refl
  | succ k ih =>
    rw [Function.iterate_succ_apply', pass_eq]
    exact ReachS.foldl _ _ _ _ _ _ (fun r hr => hr) _ ih

theorem runSections_some {Ω₀ : Set (Obligation Voc)} (hΩ : Ω₀.Finite) (σ : Trace Voc.toSignature) :
    ∀ (gs : List (ℕ × List (EClause Voc × Item Voc))), (∀ g ∈ gs, ∀ p ∈ g.2, U.SecRule g.1 p) →
      ∀ x, I.Inv Ω₀ (Trace.len σ) x →
        ∃ z, runSections U.P (gs.map toSec) (TablesOf U.L.lets I.H) I.τ I.D σ x = some z ∧
          I.Inv Ω₀ (Trace.len σ) z
  | [], _, x, hx => ⟨x, rfl, hx⟩
  | g :: gs, hg, x, hx => by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (I.section_some hΩ σ (hg g (by simp)) hx)
    have hrp := repeat_pass U.P (TablesOf U.L.lets I.H) I.τ I.D σ hy
    have hyI := hx.reach I σ (hg g (by simp)) hrp.1
    obtain ⟨z, hz, hzI⟩ := runSections_some hΩ σ gs (fun g' hg' => hg g' (by simp [hg'])) y hyI
    refine ⟨z, ?_, hzI⟩
    simp only [List.map_cons, runSections, runSection, toSec]
    rw [hy]; exact hz

/-- **`Saturate` terminates.** -/
theorem saturate_some {Ω₀ : Set (Obligation Voc)} (hΩ : Ω₀.Finite) (TN : Tables Voc)
    (σ : Trace Voc.toSignature) :
    ∃ T' C S Ω, Saturate U.P ⟨TablesOf U.L.lets I.H, I.τ, I.D, I.C₀, ∅⟩ TN Ω₀ σ = some (T', C, S, Ω) ∧
      I.Inv Ω₀ (Trace.len σ) (Ω, C, S) := by
  obtain ⟨rules, -, hrules, hsec⟩ := U.prog_spec
  have hmem : ∀ p ∈ rules, U.SecRule (U.rk p.1.ε.name) p := by
    intro p hp
    obtain ⟨c, hc, rfl, hspec⟩ := forall₂_mem_right hrules p hp
    exact ⟨(U.hrs _).1 (List.mem_mergeSort.1 hc), hspec, rfl⟩
  have hgs : ∀ g ∈ groupByRk U.rk rules, ∀ p ∈ g.2, U.SecRule g.1 p := by
    intro g hg p hp
    have hpr : p ∈ rules := by
      rw [← groupByRk_flatten U.rk rules]; simp only [List.mem_flatten, List.mem_map]
      exact ⟨g.2, ⟨g, hg, rfl⟩, hp⟩
    have := hmem p hpr
    rwa [(groupByRk_rank U.rk rules g hg).2 p hp] at this
  obtain ⟨⟨Ω, C, S⟩, hz, hzI⟩ := I.runSections_some hΩ σ _ hgs _ (Inv.init I Ω₀ (Trace.len σ))
  unfold Saturate
  simp only [hsec, hz, Option.map_some]
  exact ⟨_, C, S, Ω, rfl, hzI⟩

end TIn

end Setup

end Paper
