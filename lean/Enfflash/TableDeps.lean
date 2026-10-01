/-
  Enfflash formalization — dependency and data-flow properties of the
  concrete tables (discharging the corresponding hypotheses of the
  dependency analysis).

  * `tables_letDeps`: the let interpretation of the tables only depends on
    the events `ldOf Γ p` defining each let (transitively), as used for the
    Event Dependency Graph.
  * `tables_letsFlow`: the values of let tuples are known values (constants
    of the guards, values stored in the tables) or come from the positions
    `lsrcOf gd p i` of the working set, computed from the guards `gd` of the
    lets' operands (as computed by `TypeLet`), as used for the Data-Flow
    Graph.
  * `tabInv_commit`: tables stay finite.
-/
import Enfflash.TableImpl
import Enfflash.EDG
import Enfflash.AggImg
import Enfflash.GuardTypes

namespace Enfflash

variable {B D : Type}

/-! ## Dependencies of lets on events -/

/-- Events read by a let body on the current working set (a `prev` let only
    reads its lagged table). -/
def LBody.evsWith (ld : ℕ → List (Ev B ℕ)) : LBody B ℕ D → List (Ev B ℕ)
  | .now φ => φ.evs ld
  | .since _ _ φl φr => φl.evs ld ++ φr.evs ld
  | .agg _ _ _ _ φ => φ.evs ld
  | .prev _ _ _ => []

section
variable (Γ : List (LetDef B ℕ D))

def ldUpTo : ℕ → ℕ → List (Ev B ℕ)
  | 0 => fun _ => []
  | n + 1 => fun q => if q < n then ldUpTo n q else if q = n then
      (match Γ[n]? with
       | some d => d.body.evsWith (ldUpTo n)
       | none => [])
      else []

/-- The events each let depends on (transitively). -/
def ldOf (q : ℕ) : List (Ev B ℕ) := ldUpTo Γ (q + 1) q

end

theorem ldUpTo_stable (Γ : List (LetDef B ℕ D)) :
    ∀ m q, q < m → ldUpTo Γ m q = ldOf Γ q
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, q, h => by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | rfl
    · simp only [ldUpTo, h', if_true]; exact ldUpTo_stable Γ n q h'
    · rfl

theorem ldOf_eq (Γ : List (LetDef B ℕ D)) {p : ℕ} {d : LetDef B ℕ D} (hd : Γ[p]? = some d) :
    ldOf Γ p = d.body.evsWith (ldUpTo Γ p) := by
  simp [ldOf, ldUpTo, hd]

theorem lets_evs {L : Type} {ld : L → List (Ev B L)} (φ : Fm B L D) :
    ∀ q ∈ φ.lets, ∀ e ∈ ld q, e ∈ φ.evs ld := by
  induction φ with
  | pred p ts =>
    intro q hq e he
    cases p with
    | ev => simp [Fm.lets] at hq
    | lp p => simp only [Fm.lets, List.mem_singleton] at hq; subst hq; exact he
  | tt | eq => intro q hq; simp [Fm.lets] at hq
  | neg φ ih | ex φ ih | ev _ _ φ ih | nx _ _ φ ih => exact ih
  | conj φ ψ ih₁ ih₂ =>
    intro q hq e he
    simp only [Fm.lets, List.mem_append] at hq
    simp only [Fm.evs, List.mem_append]
    rcases hq with hq | hq
    exacts [Or.inl (ih₁ q hq e he), Or.inr (ih₂ q hq e he)]

/-- Evaluation on a single-point trace only reads the formula's events and
    the let values it refers to. -/
theorem sat_ptTr_congr {L : Type} {W W' : DB B L D} {lv lv' : L → List D → Prop}
    {ld : L → List (Ev B L)} (φ : Fm B L D)
    (hW : ∀ e ∈ φ.evs ld, ∀ as, (e, as) ∈ W ↔ (e, as) ∈ W')
    (hlv : ∀ q ∈ φ.lets, lv q = lv' q) :
    ∀ i w, (ptTr W lv).sat i w φ ↔ (ptTr W' lv').sat i w φ := by
  induction φ with
  | tt | eq => intros; rfl
  | pred p ts =>
    intro i w
    cases p with
    | ev e => exact hW e (by simp [Fm.evs]) _
    | lp p => simp only [Tr.sat, Tr.prIn, ptTr]; rw [hlv p (by simp [Fm.lets])]
  | neg φ ih => intro i w; simp only [Tr.sat]; rw [ih hW hlv]
  | ex φ ih => intro i w; simp only [Tr.sat]; exact exists_congr fun d => ih hW hlv i _
  | conj φ ψ ih₁ ih₂ =>
    intro i w
    simp only [Tr.sat]
    rw [ih₁ (fun e he => hW e (by simp [Fm.evs, he])) (fun q hq => hlv q (by simp [Fm.lets, hq])),
      ih₂ (fun e he => hW e (by simp [Fm.evs, he])) (fun q hq => hlv q (by simp [Fm.lets, hq]))]
  | ev a b φ ih =>
    intro i w
    simp only [Tr.sat, ptTr]
    exact exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => ih hW hlv j w
  | nx a b φ ih => intro i w; simp only [Tr.sat]; exact and_congr_right fun _ => ih hW hlv _ w

/-- **The tables' let interpretation depends only on `ldOf`.** -/
theorem tables_letDeps (Γ : List (LetDef B ℕ D)) (v₀ : ℕ → D) (hord : LetsOrdered Γ)
    (tab : Tab D) (t : ℕ) : ∀ (W W' : DB B ℕ D) (p : ℕ),
      (∀ e ∈ ldOf Γ p, ∀ as, (e, as) ∈ W ↔ (e, as) ∈ W') →
      lvOf Γ v₀ tab t W p = lvOf Γ v₀ tab t W' p := by
  intro W W' p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  intro hag
  funext as
  rcases hd : Γ[p]? with _ | d
  · simp [lvOf, lvUpTo, hd]
  have hord' : ∀ q ∈ d.body.lets, q < p := hord p d hd
  have hldp := ldOf_eq Γ hd
  -- operands only read events of `ldOf p` and earlier lets
  have hop : ∀ φ : Fm B ℕ D, (∀ e ∈ φ.evs (ldUpTo Γ p), e ∈ d.body.evsWith (ldUpTo Γ p)) →
      (∀ q ∈ φ.lets, q ∈ d.body.lets) → ∀ as,
      sat0 v₀ W (lvOf Γ v₀ tab t W) φ as ↔ sat0 v₀ W' (lvOf Γ v₀ tab t W') φ as := by
    intro φ hev hl as
    refine sat_ptTr_congr (ld := ldUpTo Γ p) φ (fun e he => hag e (hldp ▸ hev e he)) ?_ 0 _
    intro q hq
    have hqp := hord' q (hl q hq)
    refine ih q hqp fun e he => hag e (hldp ▸ hev e ?_)
    rw [← ldUpTo_stable Γ p q hqp] at he
    exact lets_evs φ q hq e he
  rw [propext (lvOf_eq Γ v₀ hord tab t W hd as), propext (lvOf_eq Γ v₀ hord tab t W' hd as)]
  refine propext (and_congr_right fun _ => ?_)
  cases hb : d.body with
  | now φ =>
    exact hop φ (by simp [hb, LBody.evsWith]) (by simp [hb, LBody.lets]) as
  | since a b φl φr =>
    simp only [bodyVal]
    rw [hop φl (by intro e he; simp [hb, LBody.evsWith, he]) (by intro q hq; simp [hb, LBody.lets, hq]) as,
      hop φr (by intro e he; simp [hb, LBody.evsWith, he]) (by intro q hq; simp [hb, LBody.lets, hq]) as]
  | prev => rfl
  | agg k ω ts ys φ =>
    simp only [bodyVal]
    refine aggSem_congr (fun ds _ => ?_) (fun _ _ => rfl) rfl
    refine sat_ptTr_congr (ld := ldUpTo Γ p) φ
      (fun e he => hag e (hldp ▸ by simp [hb, LBody.evsWith, he])) ?_ 0 _
    intro q hq
    have hqp := hord' q (by simp [hb, LBody.lets, hq])
    refine ih q hqp fun e he => hag e (hldp ▸ ?_)
    rw [← ldUpTo_stable Γ p q hqp] at he
    simpa [hb, LBody.evsWith] using lets_evs φ q hq e he

/-! ## Guards of let operands -/

section
variable {L : Type}

def GAtom.lets : GAtom B L D → List L
  | .pred (.lp q) _ => [q]
  | _ => []

theorem Guards.toFm_lets {π : Guards B L D} {q : L} (h : q ∈ π.toFm.lets) :
    ∃ κ ∈ π, ∃ a ∈ κ, ∃ ts, a = .pred (.lp q) ts := by
  induction π with
  | nil => simp [Guards.toFm, Fm.lets] at h
  | cons κ π ih =>
    simp only [Guards.toFm, Fm.disj, Fm.lets, List.mem_append] at h
    rcases h with h | h
    · refine ⟨κ, List.mem_cons_self .., ?_⟩
      induction κ with
      | nil => simp [Guards.conjFm, Fm.lets] at h
      | cons a κ ihκ =>
        simp only [Guards.conjFm, List.foldr_cons, Fm.lets, List.mem_append] at h ihκ
        rcases h with h | h
        · refine ⟨a, List.mem_cons_self .., ?_⟩
          rcases a with ⟨p, ts⟩ | ⟨t, d⟩
          · cases p with
            | ev => simp [GAtom.toFm, Fm.lets] at h
            | lp p => simp [GAtom.toFm, Fm.lets] at h; exact ⟨ts, by rw [h]⟩
          · simp [GAtom.toFm, Fm.lets] at h
        · obtain ⟨a', ha', h'⟩ := ihκ h
          exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩
    · obtain ⟨κ', hκ', rest⟩ := ih h
      exact ⟨κ', List.mem_cons_of_mem _ hκ', rest⟩

/-- Let atoms moved into guards are enumerable and come from the original
    formula. -/
theorem GX.letInv {m : Pr B L → Prop} {S : Set L} {x : ℕ} {p : Bool} {π π' : Guards B L D}
    {φ φ' : Fm B L D} (h : GX m x p π φ π' φ')
    (hπ : ∀ κ ∈ π, ∀ a ∈ κ, ∀ q ts, a = .pred (.lp q) ts → m (.lp q) ∧ q ∈ S)
    (hφ : ∀ q ∈ φ.lets, q ∈ S) :
    (∀ κ ∈ π', ∀ a ∈ κ, ∀ q ts, a = .pred (.lp q) ts → m (.lp q) ∧ q ∈ S) ∧
      (∀ q ∈ φ'.lets, q ∈ S) := by
  induction h with
  | grd => exact ⟨hπ, hφ⟩
  | vacPos | vacNeg => exact ⟨by simp, by simp [Fm.lets]⟩
  | @pred π p ts hm _ =>
    refine ⟨fun κ' hκ' a ha q ts' he => ?_, by simp [Fm.lets]⟩
    obtain ⟨κ, hκ, rfl⟩ := List.mem_map.1 hκ'
    rcases List.mem_append.1 ha with ha | ha
    · exact hπ κ hκ a ha q ts' he
    · rw [List.mem_singleton] at ha; subst ha
      cases he
      exact ⟨hm, hφ q (by simp [Fm.lets])⟩
  | eq =>
    refine ⟨fun κ' hκ' a ha q ts' he => ?_, by simp [Fm.lets]⟩
    obtain ⟨κ, hκ, rfl⟩ := List.mem_map.1 hκ'
    rcases List.mem_append.1 ha with ha | ha
    · exact hπ κ hκ a ha q ts' he
    · rw [List.mem_singleton] at ha; subst ha; cases he
  | neg _ ih => exact ih hπ hφ
  | andL _ ih =>
    obtain ⟨h1, h2⟩ := ih hπ fun q hq => hφ q (by simp [Fm.lets, hq])
    refine ⟨h1, fun q hq => ?_⟩
    simp only [Fm.lets, List.mem_append] at hq
    rcases hq with hq | hq
    exacts [h2 q hq, hφ q (by simp [Fm.lets, hq])]
  | andR _ ih =>
    obtain ⟨h1, h2⟩ := ih hπ fun q hq => hφ q (by simp [Fm.lets, hq])
    refine ⟨h1, fun q hq => ?_⟩
    simp only [Fm.lets, List.mem_append] at hq
    rcases hq with hq | hq
    exacts [hφ q (by simp [Fm.lets, hq]), h2 q hq]
  | andNeg _ _ ih₁ ih₂ =>
    obtain ⟨h1, h2⟩ := ih₁ hπ fun q hq => hφ q (by simp [Fm.lets, hq])
    obtain ⟨g1, g2⟩ := ih₂ hπ fun q hq => hφ q (by simp [Fm.lets, hq])
    refine ⟨fun κ hκ => (List.mem_append.1 hκ).elim (h1 κ) (g1 κ), fun q hq => ?_⟩
    simp only [Fm.lets, impFm, Fm.disj, List.mem_append] at hq
    rcases hq with (hq | hq) | (hq | hq)
    · obtain ⟨κ, hκ, a, ha, ts, rfl⟩ := Guards.toFm_lets hq; exact (h1 κ hκ _ ha q ts rfl).2
    · exact h2 q hq
    · obtain ⟨κ, hκ, a, ha, ts, rfl⟩ := Guards.toFm_lets hq; exact (g1 κ hκ _ ha q ts rfl).2
    · exact g2 q hq

end

/-- The operand producing a let's tuples. -/
def LBody.valOp : LBody B ℕ D → Option (Fm B ℕ D)
  | .now φ => some φ
  | .since _ _ _ φr => some φr
  | .prev _ _ φ => some φ
  | .agg _ _ _ _ φ => some φ

theorem LBody.valOp_lets {body : LBody B ℕ D} {φ : Fm B ℕ D} (h : body.valOp = some φ) :
    ∀ q ∈ φ.lets, q ∈ body.lets := by
  intro q hq
  cases body <;> simp [valOp] at h <;> subst h <;> simp [LBody.lets, hq]

/-- Enumerable predicates: events, and lets with guards. -/
def enumOf (gd : ℕ → Option (Guards B ℕ D)) : Pr B ℕ → Prop
  | .ev _ => True
  | .lp q => (gd q).isSome

/-- Strip the leading existentials of a formula. -/
def Fm.stripEx {L : Type} : Fm B L D → ℕ × Fm B L D
  | .ex φ => (φ.stripEx.1 + 1, φ.stripEx.2)
  | φ => (0, φ)

theorem Tr.sat_stripEx {L : Type} (σ : Tr B L D) (i : ℕ) (φ : Fm B L D) :
    ∀ w, σ.sat i w φ ↔ ∃ ds : List D, ds.length = φ.stripEx.1 ∧ σ.sat i (vapp ds w) φ.stripEx.2 := by
  induction φ with
  | ex φ ih =>
    intro w
    simp only [Fm.stripEx, Tr.sat]
    constructor
    · rintro ⟨d, hd⟩
      obtain ⟨ds, hl, h⟩ := (ih _).1 hd
      exact ⟨ds ++ [d], by simp [hl], by rw [vapp_append]; exact h⟩
    · rintro ⟨ds, hl, h⟩
      obtain ⟨ds', d, rfl⟩ : ∃ ds' d, ds = ds' ++ [d] := by
        rcases List.eq_nil_or_concat ds with rfl | ⟨ds', d, rfl⟩
        · simp at hl
        · exact ⟨ds', d, by simp⟩
      rw [vapp_append] at h
      exact ⟨d, (ih _).2 ⟨ds', by simpa using hl, h⟩⟩
  | _ => intro w; simp [Fm.stripEx]

theorem Fm.lets_stripEx {L : Type} (φ : Fm B L D) : φ.stripEx.2.lets = φ.lets := by
  induction φ with
  | ex φ ih => simpa [Fm.stripEx, Fm.lets] using ih
  | _ => rfl

namespace LetDef

/-- The formula whose satisfying valuations produce the let's tuples: the
    value-producing operand without its leading existentials, or the operand
    of an aggregation (whose satisfying valuations form the groups). -/
def gop (d : LetDef B ℕ D) : Option (Fm B ℕ D) :=
  match d.body with
  | .agg _ _ _ _ φ => some φ
  | b => b.valOp.map fun φ => φ.stripEx.2

/-- The number of variables of `gop` bound before the let's arguments (the
    stripped existentials, or the aggregated variables). -/
def off (d : LetDef B ℕ D) : ℕ :=
  match d.body with
  | .agg k _ _ _ _ => k
  | b => (b.valOp.map fun φ => φ.stripEx.1).getD 0

/-- Argument `i` is a result of an aggregation. -/
def isRes (d : LetDef B ℕ D) (i : ℕ) : Bool :=
  match d.body with
  | .agg _ _ _ ys _ => ys.contains i
  | _ => false

/-- The variables of `gop` that must be guarded: the bound ones and the
    arguments, except the aggregation results. -/
def gvars (d : LetDef B ℕ D) : List ℕ :=
  List.range d.off ++ ((List.range d.arity).filter fun i => !d.isRes i).map (· + d.off)

theorem mem_gvars_off {d : LetDef B ℕ D} {m : ℕ} (h : m < d.off) : m ∈ d.gvars :=
  List.mem_append_left _ (List.mem_range.2 h)

theorem mem_gvars_arg {d : LetDef B ℕ D} {i : ℕ} (h : i < d.arity) (hr : d.isRes i = false) :
    i + d.off ∈ d.gvars :=
  List.mem_append_right _
    (List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_range.2 h, by simp [hr]⟩, rfl⟩)

theorem gop_lets {d : LetDef B ℕ D} {φ : Fm B ℕ D} (h : d.gop = some φ) :
    ∀ q ∈ φ.lets, q ∈ d.body.lets := by
  intro q hq
  unfold gop at h
  split at h
  · rename_i hb; cases h; simp [hb, LBody.lets, hq]
  · obtain ⟨ψ, hψ, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [Fm.lets_stripEx] at hq
    exact LBody.valOp_lets hψ q hq

/-- For lets other than aggregations, `gop` is the stripped operand. -/
theorem gop_valOp {d : LetDef B ℕ D} {φ : Fm B ℕ D} (hvo : d.body.valOp = some φ)
    (hna : ∀ k ω ts ys ψ, d.body ≠ .agg k ω ts ys ψ) :
    d.gop = some φ.stripEx.2 ∧ d.off = φ.stripEx.1 ∧ ∀ i, d.isRes i = false := by
  rcases hb : d.body with ψ | ⟨a, b, ψl, ψr⟩ | ⟨a, b, ψ⟩ | ⟨k, ω, ts, ys, ψ⟩ <;>
    rw [hb] at hvo <;> simp only [LBody.valOp, Option.some.injEq] at hvo
  all_goals first
    | exact absurd hb (hna _ _ _ _ _)
    | (subst hvo; exact ⟨by simp [gop, hb, LBody.valOp], by simp [off, hb, LBody.valOp],
        fun i => by simp [isRes, hb]⟩)

end LetDef

/-- The guards computed by `TypeLet` for each guardable let: joint guards
    for all variables of `gop` except the aggregation results; temporal lets
    and aggregations must be guardable, present lets without guards are
    filter-only; the left operand of a since let must be enumerable in
    negative polarity (its `remove` clause); the terms of an aggregation are
    well-formed and only read guarded variables. -/
structure LetGuards (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D)) : Prop where
  guards : ∀ p (d : LetDef B ℕ D) π, Γ[p]? = some d → gd p = some π →
    ∃ φ φ', d.gop = some φ ∧ GXJ (enumOf gd) d.gvars true φ π φ'
  removal : ∀ p (d : LetDef B ℕ D) a b φl φr, Γ[p]? = some d → d.body = .since a b φl φr →
    (gd p).isSome → Enum (enumOf gd) (List.range d.arity) false φl
  temporal : ∀ p (d : LetDef B ℕ D), Γ[p]? = some d →
    (∀ a b φl φr, d.body = .since a b φl φr → (gd p).isSome) ∧
    (∀ a b φ, d.body = .prev a b φ → (gd p).isSome) ∧
    (∀ k ω ts ys φ, d.body = .agg k ω ts ys φ → (gd p).isSome)
  aggTerms : ∀ (p : ℕ) (d : LetDef B ℕ D) k ω ts ys φ, Γ[p]? = some d →
    d.body = .agg k ω ts ys φ → ∀ t ∈ ts, t.WF ∧ ∀ x ∈ t.supp, x ∈ d.gvars

theorem LetGuards.aggWF {Γ : List (LetDef B ℕ D)} {gd : ℕ → Option (Guards B ℕ D)}
    (hg : LetGuards Γ gd) : AggWF Γ := by
  intro d hd k ω ts ys φ hb t ht
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hd
  exact (hg.aggTerms p d k ω ts ys φ hp hb t ht).1

/-- Let atoms in joint guards are enumerable and come from the formula. -/
theorem GXJ.letInv {L : Type} {m : Pr B L → Prop} {X : List ℕ} {p : Bool} {φ φ' : Fm B L D}
    {π : Guards B L D} (h : GXJ m X p φ π φ') :
    ∀ κ ∈ π, ∀ a ∈ κ, ∀ q ts, a = .pred (.lp q) ts → m (.lp q) ∧ q ∈ φ.lets := by
  induction h with
  | none => intro κ hκ a ha; simp at hκ; subst hκ; simp at ha
  | vac => intro κ hκ; simp at hκ
  | pred hm _ =>
    intro κ hκ a ha q ts he
    simp at hκ; subst hκ; simp at ha; subst ha; cases he; exact ⟨hm, by simp [Fm.lets]⟩
  | eq => intro κ hκ a ha q ts he; simp at hκ; subst hκ; simp at ha; subst ha; cases he
  | neg _ ih => exact ih
  | andPos _ _ _ ih₁ ih₂ =>
    intro κ hκ a ha q ts he
    simp only [Guards.prod, List.mem_flatMap, List.mem_map] at hκ
    obtain ⟨κ₁, h₁, κ₂, h₂, rfl⟩ := hκ
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨hm, hq⟩ := ih₁ κ₁ h₁ a ha q ts he; exact ⟨hm, by simp [Fm.lets, hq]⟩
    · obtain ⟨hm, hq⟩ := ih₂ κ₂ h₂ a ha q ts he; exact ⟨hm, by simp [Fm.lets, hq]⟩
  | andNeg _ _ ih₁ ih₂ =>
    intro κ hκ a ha q ts he
    rcases List.mem_append.1 hκ with h | h
    · obtain ⟨hm, hq⟩ := ih₁ κ h a ha q ts he; exact ⟨hm, by simp [Fm.lets, hq]⟩
    · obtain ⟨hm, hq⟩ := ih₂ κ h a ha q ts he; exact ⟨hm, by simp [Fm.lets, hq]⟩

/-! ## Source positions of let values -/

def Term.isVarOf (i : ℕ) : Term D → Bool
  | .var n => n == i
  | _ => false

def atomSrc (ls : ℕ → ℕ → List (Pos B ℕ)) (i : ℕ) : GAtom B ℕ D → List (Pos B ℕ)
  | .pred (.ev e) ts =>
    ((List.range ts.length).filter fun j => (ts[j]?).any (Term.isVarOf i)).map fun j => (e, j)
  | .pred (.lp q) ts =>
    (List.range ts.length).flatMap fun j => if (ts[j]?).any (Term.isVarOf i) then ls q j else []
  | .eq _ _ => []

/-- Non-stable sources of variable `i` in a guard atom: the non-stable
    sources `ls` of the let arguments it binds. -/
def atomSrcN (ls : ℕ → ℕ → List (Pos B ℕ)) (i : ℕ) : GAtom B ℕ D → List (Pos B ℕ)
  | .pred (.lp q) ts =>
    (List.range ts.length).flatMap fun j => if (ts[j]?).any (Term.isVarOf i) then ls q j else []
  | _ => []

/-- The stable and non-stable sources of variable `x` in the guards `π`,
    given the sources `ls` of the arguments of earlier lets. -/
def varSrc (ls : ℕ → ℕ → List (Pos B ℕ) × List (Pos B ℕ)) (π : Guards B ℕ D) (x : ℕ) :
    List (Pos B ℕ) × List (Pos B ℕ) :=
  (π.flatMap fun κ => κ.flatMap (atomSrc (fun q j => (ls q j).1) x),
   π.flatMap fun κ => κ.flatMap (atomSrcN (fun q j => (ls q j).2) x))

/-- The sources of argument `i` of let `d` with guards `π`: those of the
    corresponding variable of `gop`, or, for an aggregation result, all
    sources of the guarded variables (non-stable). -/
def argSrc (ls : ℕ → ℕ → List (Pos B ℕ) × List (Pos B ℕ)) (π : Guards B ℕ D)
    (d : LetDef B ℕ D) (i : ℕ) : List (Pos B ℕ) × List (Pos B ℕ) :=
  if d.isRes i then ([], d.gvars.flatMap fun x => (varSrc ls π x).1 ++ (varSrc ls π x).2)
  else varSrc ls π (i + d.off)

section
variable (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D))

def srcUpTo : ℕ → ℕ → ℕ → List (Pos B ℕ) × List (Pos B ℕ)
  | 0 => fun _ _ => ([], [])
  | n + 1 => fun q i => if q < n then srcUpTo n q i else if q = n then
      (match Γ[n]? with
       | some d => argSrc (srcUpTo n) ((gd n).getD []) d i
       | none => ([], []))
      else ([], [])

/-- The sources of argument `i` of let `q`. -/
def srcOf (q i : ℕ) : List (Pos B ℕ) × List (Pos B ℕ) := srcUpTo Γ gd (q + 1) q i

/-- Positions from which the `i`-th argument of let `q` can come (stable). -/
def lsrcOf (q i : ℕ) : List (Pos B ℕ) := (srcOf Γ gd q i).1

/-- Positions from whose values the `i`-th argument of let `q` can be
    computed by aggregation (non-stable). -/
def nsrcOf (q i : ℕ) : List (Pos B ℕ) := (srcOf Γ gd q i).2

end

theorem srcUpTo_stable (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D)) :
    ∀ m q, q < m → srcUpTo Γ gd m q = srcOf Γ gd q
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, q, h => by
    funext i
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h) with h' | rfl
    · simp only [srcUpTo, h', if_true]; rw [srcUpTo_stable Γ gd n q h']
    · rfl

theorem srcOf_eq (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D)) {p : ℕ}
    {d : LetDef B ℕ D} (hd : Γ[p]? = some d) (i : ℕ) :
    srcOf Γ gd p i = argSrc (srcUpTo Γ gd p) ((gd p).getD []) d i := by
  simp [srcOf, srcUpTo, hd]

/-! ## Data flow -/

section
variable (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D))

/-- Constants of equality guards. -/
def guardConsts : Set D :=
  {c | ∃ p < Γ.length, ∃ π, gd p = some π ∧ ∃ κ ∈ π, ∃ t, GAtom.eq t c ∈ κ}

/-- Values stored in the tables. -/
def tabVals (tab : Tab D) : Set D :=
  {c | ∃ n r, (r ∈ tab.since n ∨ r ∈ tab.lag n) ∧ c ∈ r.2}

end

theorem guardConsts_finite (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D)) :
    (guardConsts Γ gd).Finite := by
  let f : GAtom B ℕ D → Set D := fun a => match a with | .eq _ c => {c} | _ => ∅
  have hf : ∀ a, (f a).Finite := by intro a; rcases a with _ | _ <;> simp [f]
  refine (Set.Finite.biUnion (Set.finite_lt_nat Γ.length) fun p _ =>
    Set.Finite.biUnion (List.finite_toSet ((gd p).getD [])) fun κ _ =>
      Set.Finite.biUnion (t := fun a => f a) (List.finite_toSet κ) fun a _ => hf a).subset ?_
  · rintro c ⟨p, hp, π, hπ, κ, hκ, t, ht⟩
    simp only [Set.mem_iUnion]
    exact ⟨p, hp, κ, by simp [hπ, hκ], _, ht, by simp [f]⟩

theorem tabVals_finite {Γ : List (LetDef B ℕ D)} {tab : Tab D} (h : TabInv Γ tab) :
    (tabVals tab).Finite := by
  refine (Set.Finite.biUnion (Set.finite_lt_nat Γ.length) fun n _ =>
    Set.Finite.biUnion ((h n).1.union (h n).2.1) fun r _ => List.finite_toSet r.2).subset ?_
  rintro c ⟨n, r, hr, hc⟩
  simp only [Set.mem_iUnion]
  refine ⟨n, ?_, r, hr, hc⟩
  by_contra hn
  have := (h n).2.2 (by simp at hn; omega)
  rcases hr with hr | hr
  · rw [this.1] at hr; exact hr
  · rw [this.2] at hr; exact hr

/-! ### Values of let tuples -/

/-- Known values: constants of the guards and values stored in the tables. -/
abbrev known (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D)) (tab : Tab D) :
    Set D :=
  guardConsts Γ gd ∪ tabVals tab

/-- The values at the positions `qs`. -/
def valsOf (W : DB B ℕ D) (qs : List (Pos B ℕ)) : Set D := {c | ∃ q ∈ qs, c ∈ valsAt W q}

/-- A value is known, is at one of the stable sources `ss`, or is computed by
    at most `n` rounds of aggregation from known values and the values at the
    non-stable sources `ns`. -/
def FlowVal (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D)) (tab : Tab D)
    (W : DB B ℕ D) (n : ℕ) (ss ns : List (Pos B ℕ)) (c : D) : Prop :=
  c ∈ known Γ gd tab ∨ c ∈ valsOf W ss ∨ c ∈ aggClo Γ n (known Γ gd tab ∪ valsOf W ns)

theorem FlowVal.mono {Γ : List (LetDef B ℕ D)} {gd : ℕ → Option (Guards B ℕ D)} {tab : Tab D}
    {W : DB B ℕ D} {n n' : ℕ} {ss ss' ns ns' : List (Pos B ℕ)} {c : D}
    (h : FlowVal Γ gd tab W n ss ns c) (hn : n ≤ n') (hs : ss ⊆ ss') (hns : ns ⊆ ns') :
    FlowVal Γ gd tab W n' ss' ns' c := by
  rcases h with h | ⟨q, hq, hv⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨q, hs hq, hv⟩)
  · refine Or.inr (Or.inr (aggClo_le hn _ (aggClo_mono n ?_ h)))
    exact Set.union_subset_union le_rfl fun c ⟨q, hq, hv⟩ => ⟨q, hns hq, hv⟩

/-- The conclusion of the flow analysis for a tuple of let `p`. -/
def FlowConcl (Γ : List (LetDef B ℕ D)) (gd : ℕ → Option (Guards B ℕ D)) (tab : Tab D)
    (W : DB B ℕ D) (p : ℕ) (as : List D) : Prop :=
  ∀ i c, as[i]? = some c → FlowVal Γ gd tab W (p + 1) (lsrcOf Γ gd p i) (nsrcOf Γ gd p i) c

section
variable {Γ : List (LetDef B ℕ D)} {v₀ : ℕ → D} {gd : ℕ → Option (Guards B ℕ D)}
  (hord : LetsOrdered Γ) (hg : LetGuards Γ gd) (tab : Tab D) (t : ℕ) (W : DB B ℕ D)

include hord hg in
/-- **Data flow of the tables.**  By induction along the let order: the
    values of the guarded variables of any valuation satisfying `gop` of a
    let, and the values of the tuples of a let, are known, come from the
    working set at their stable sources, or are computed by aggregation from
    the values at their non-stable sources. -/
theorem flow : ∀ p,
    (∀ π (d : LetDef B ℕ D) φ (w : ℕ → D), gd p = some π → Γ[p]? = some d → d.gop = some φ →
      (ptTr W (lvOf Γ v₀ tab t W)).sat 0 w φ → ∀ x ∈ d.gvars,
        FlowVal Γ gd tab W p (varSrc (srcUpTo Γ gd p) π x).1 (varSrc (srcUpTo Γ gd p) π x).2
          (w x)) ∧
    ((gd p).isSome → ∀ as, lvOf Γ v₀ tab t W p as → FlowConcl Γ gd tab W p as) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
  have hvar : ∀ π (d : LetDef B ℕ D) φ (w : ℕ → D), gd p = some π → Γ[p]? = some d →
      d.gop = some φ → (ptTr W (lvOf Γ v₀ tab t W)).sat 0 w φ → ∀ x ∈ d.gvars,
        FlowVal Γ gd tab W p (varSrc (srcUpTo Γ gd p) π x).1 (varSrc (srcUpTo Γ gd p) π x).2
          (w x) := by
    intro π d φ w hgp hd hgop hsat x hx
    obtain ⟨φ₀, φ', hgop', hgx⟩ := hg.guards p d π hd hgp
    rw [hgop] at hgop'; cases hgop'
    obtain ⟨hsound, hbind⟩ := hgx.sound
    obtain ⟨κ, hκ, hall⟩ :=
      ((hsound (ptTr W (lvOf Γ v₀ tab t W)) 0 w).1 ⟨Guards.sat_top _ _ _, hsat⟩).1
    obtain ⟨a, ha, hab⟩ := hbind x hx κ hκ
    have hs1 : ∀ l, l ⊆ atomSrc (fun q j => (srcUpTo Γ gd p q j).1) x a →
        l ⊆ (varSrc (srcUpTo Γ gd p) π x).1 :=
      fun l hl r hr => List.mem_flatMap.2 ⟨κ, hκ, List.mem_flatMap.2 ⟨a, ha, hl hr⟩⟩
    have hs2 : ∀ l, l ⊆ atomSrcN (fun q j => (srcUpTo Γ gd p q j).2) x a →
        l ⊆ (varSrc (srcUpTo Γ gd p) π x).2 :=
      fun l hl r hr => List.mem_flatMap.2 ⟨κ, hκ, List.mem_flatMap.2 ⟨a, ha, hl hr⟩⟩
    have hsa := hall a ha
    rcases a with ⟨pr, ts⟩ | ⟨t', c'⟩
    · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hab
      have hval : (ts.map (Term.eval w))[j]? = some (w x) := by
        rw [List.getElem?_map, hj]; rfl
      have hjl : j < ts.length := (List.getElem?_eq_some_iff.1 hj).1
      cases pr with
      | ev e =>
        refine Or.inr (Or.inl ⟨(e, j), hs1 [(e, j)] ?_ (List.mem_singleton_self _), _, hsa, hval⟩)
        intro r hr
        rw [List.mem_singleton] at hr; subst hr
        simp only [atomSrc, List.mem_map, List.mem_filter, List.mem_range]
        exact ⟨j, ⟨hjl, by simp [hj, Term.isVarOf]⟩, rfl⟩
      | lp q =>
        -- a guard on an earlier, enumerable let
        obtain ⟨hq, hqS⟩ := hgx.letInv κ hκ _ ha q ts rfl
        have hqp : q < p := hord p d hd q (LetDef.gop_lets hgop q hqS)
        simp only [GAtom.sat, Tr.prIn, ptTr] at hsa
        have hfl := (ih q hqp).2 hq _ hsa j (w x) hval
        refine hfl.mono (by omega) (hs1 _ fun r hr => ?_) (hs2 _ fun r hr => ?_)
        · simp only [atomSrc, List.mem_flatMap, List.mem_range]
          refine ⟨j, hjl, ?_⟩
          simp only [hj, Option.any_some, Term.isVarOf, beq_self_eq_true, if_true]
          rw [srcUpTo_stable Γ gd p q hqp]; exact hr
        · simp only [atomSrcN, List.mem_flatMap, List.mem_range]
          refine ⟨j, hjl, ?_⟩
          simp only [hj, Option.any_some, Term.isVarOf, beq_self_eq_true, if_true]
          rw [srcUpTo_stable Γ gd p q hqp]; exact hr
    · simp only [GAtom.binds] at hab; subst hab
      simp only [GAtom.sat, Term.eval] at hsa
      refine Or.inl (Or.inl ⟨p, (List.getElem?_eq_some_iff.1 hd).1, π, hgp, κ, hκ, Term.var x, ?_⟩)
      rw [hsa]; exact ha
  refine ⟨hvar, fun hp as h => ?_⟩
  obtain ⟨π, hπ⟩ := Option.isSome_iff_exists.1 hp
  rcases hd : Γ[p]? with _ | d
  · simp [lvOf, lvUpTo, hd] at h
  rw [lvOf_eq Γ v₀ hord tab t W hd] at h
  obtain ⟨hl, hb⟩ := h
  have hsrc : ∀ i, srcOf Γ gd p i = argSrc (srcUpTo Γ gd p) π d i := fun i => by
    rw [srcOf_eq Γ gd hd, hπ]; rfl
  -- a non-result argument of a tuple produced by a valuation of `gop`
  have harg : ∀ φ (ds : List D), d.gop = some φ → ds.length = d.off →
      (ptTr W (lvOf Γ v₀ tab t W)).sat 0 (vapp ds (vapp as v₀)) φ →
      ∀ i c, as[i]? = some c → d.isRes i = false →
        FlowVal Γ gd tab W (p + 1) (lsrcOf Γ gd p i) (nsrcOf Γ gd p i) c := by
    intro φ ds hgop hdl hsat i c hc hr
    have hi : i < as.length := (List.getElem?_eq_some_iff.1 hc).1
    have hw : vapp ds (vapp as v₀) (i + d.off) = c := by
      rw [← hdl, vapp_ge, vapp_lt _ _ _ hi]; exact (List.getElem?_eq_some_iff.1 hc).2
    have := hvar π d φ _ hπ hd hgop hsat (i + d.off) (LetDef.mem_gvars_arg (hl ▸ hi) hr)
    rw [hw] at this
    simp only [lsrcOf, nsrcOf, hsrc, argSrc, hr, Bool.false_eq_true, if_false]
    exact this.mono (by omega) (fun _ h => h) (fun _ h => h)
  -- the operand of a present or since let
  have hop : ∀ ψ, d.body.valOp = some ψ → (∀ k ω ts ys φ, d.body ≠ .agg k ω ts ys φ) →
      sat0 v₀ W (lvOf Γ v₀ tab t W) ψ as → FlowConcl Γ gd tab W p as := by
    intro ψ hvo hna hsat i c hc
    obtain ⟨hgop, hoff, hres⟩ := LetDef.gop_valOp hvo hna
    obtain ⟨ds, hdl, hsat'⟩ := (Tr.sat_stripEx _ 0 ψ _).1 hsat
    exact harg _ ds hgop (hdl.trans hoff.symm) hsat' i c hc (hres i)
  cases hbd : d.body with
  | now ψ =>
    rw [hbd] at hb
    exact hop ψ (by simp [hbd, LBody.valOp]) (by intros; simp [hbd]) hb
  | since a b ψl ψr =>
    rw [hbd] at hb
    obtain ⟨τ', hrow | ⟨-, hnew⟩, -⟩ := hb
    · intro i c hc
      exact Or.inl (Or.inr ⟨p, (τ', as), Or.inl hrow.1, List.mem_of_getElem? hc⟩)
    · exact hop ψr (by simp [hbd, LBody.valOp]) (by intros; simp [hbd]) hnew
  | prev a b ψ =>
    rw [hbd] at hb
    obtain ⟨τ', hrow, -⟩ := hb
    intro i c hc
    exact Or.inl (Or.inr ⟨p, (τ', as), Or.inr hrow, List.mem_of_getElem? hc⟩)
  | agg k ω ts ys φ =>
    rw [hbd] at hb
    obtain ⟨⟨ds, hdl, hsat⟩, hω⟩ := hb
    have hgop : d.gop = some φ := by simp [LetDef.gop, hbd]
    have hoff : d.off = k := by simp [LetDef.off, hbd]
    intro i c hc
    cases hr : d.isRes i
    · exact harg φ ds hgop (hdl.trans hoff.symm) hsat i c hc hr
    · -- an aggregation result
      have hys : i ∈ ys := by simpa [LetDef.isRes, hbd] using hr
      have hns : nsrcOf Γ gd p i =
          d.gvars.flatMap fun x => (varSrc (srcUpTo Γ gd p) π x).1 ++
            (varSrc (srcUpTo Γ gd p) π x).2 := by
        simp [nsrcOf, hsrc, argSrc, hr]
      set U := aggClo Γ p (known Γ gd tab ∪ valsOf W (nsrcOf Γ gd p i))
      have hU : ∀ w, (ptTr W (lvOf Γ v₀ tab t W)).sat 0 w φ → ∀ x ∈ d.gvars, w x ∈ U := by
        intro w hw x hx
        have hsub : (varSrc (srcUpTo Γ gd p) π x).1 ++ (varSrc (srcUpTo Γ gd p) π x).2 ⊆
            nsrcOf Γ gd p i := by
          rw [hns]; intro r hr; exact List.mem_flatMap.2 ⟨x, hx, hr⟩
        rcases hvar π d φ w hπ hd hgop hw x hx with h | ⟨q, hq, hv⟩ | h
        · exact aggClo_ext p _ (Or.inl h)
        · exact aggClo_ext p _ (Or.inr ⟨q, hsub (List.mem_append_left _ hq), hv⟩)
        · refine aggClo_mono p (Set.union_subset_union le_rfl ?_) h
          rintro c ⟨q, hq, hv⟩; exact ⟨q, hsub (List.mem_append_right _ hq), hv⟩
      have hmem : c ∈ aggImg k ω ts U := by
        refine ⟨_, ⟨fun r hr => ?_, fun r => ?_⟩, _, hω, ?_⟩
        · obtain ⟨ds', hl', hs', hr'⟩ := Set.nonempty_of_encard_ne_zero hr
          exact ⟨vapp ds' (vapp as v₀), fun t' ht' x hx =>
            hU _ hs' x ((hg.aggTerms p d k ω ts ys φ hd hbd t' ht').2 x hx), hr'.symm⟩
        · refine Set.encard_le_encard fun ds' hds' => ⟨hds'.1, fun e he => ?_⟩
          obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 he
          have hml : m < ds'.length := (List.getElem?_eq_some_iff.1 hm).1
          have := hU _ hds'.2.1 m (LetDef.mem_gvars_off (by rw [hoff, ← hds'.1]; exact hml))
          rwa [vapp_lt _ _ _ hml, (List.getElem?_eq_some_iff.1 hm).2] at this
        · have hi : i < as.length := (List.getElem?_eq_some_iff.1 hc).1
          refine List.mem_map.2 ⟨i, hys, ?_⟩
          rw [vapp_lt _ _ _ hi]; exact (List.getElem?_eq_some_iff.1 hc).2
      exact Or.inr (Or.inr (aggImg_clo (List.mem_of_getElem? hd) hbd p _ hmem))

include hord hg in
theorem lv_flow (p : ℕ) (hp : (gd p).isSome) (as : List D) (h : lvOf Γ v₀ tab t W p as) :
    FlowConcl Γ gd tab W p as :=
  (flow hord hg tab t W p).2 hp as h

include hord hg in
/-- Rows of a since or lagged table (a non-aggregation let) satisfying its
    operand. -/
theorem row_flow (p : ℕ) (π : Guards B ℕ D) (d : LetDef B ℕ D) (ψ : Fm B ℕ D) (as : List D)
    (hgp : gd p = some π) (hd : Γ[p]? = some d) (hvo : d.body.valOp = some ψ)
    (hna : ∀ k ω ts ys φ, d.body ≠ .agg k ω ts ys φ) (hlen : as.length = d.arity)
    (hsat : sat0 v₀ W (lvOf Γ v₀ tab t W) ψ as) : FlowConcl Γ gd tab W p as := by
  intro i c hc
  obtain ⟨hgop, hoff, hres⟩ := LetDef.gop_valOp hvo hna
  obtain ⟨ds, hdl, hsat'⟩ := (Tr.sat_stripEx _ 0 ψ _).1 hsat
  have hi : i < as.length := (List.getElem?_eq_some_iff.1 hc).1
  have hw : vapp ds (vapp as v₀) (i + d.off) = c := by
    rw [hoff, ← hdl, vapp_ge, vapp_lt _ _ _ hi]; exact (List.getElem?_eq_some_iff.1 hc).2
  have := (flow hord hg tab t W p).1 π d _ _ hgp hd hgop hsat' (i + d.off)
    (LetDef.mem_gvars_arg (hlen ▸ hi) (hres i))
  rw [hw] at this
  have hsrc : srcOf Γ gd p i = argSrc (srcUpTo Γ gd p) π d i := by rw [srcOf_eq Γ gd hd, hgp]; rfl
  simp only [lsrcOf, nsrcOf, hsrc, argSrc, hres i, Bool.false_eq_true, if_false]
  exact this.mono (by omega) (fun _ h => h) (fun _ h => h)

end

/-- All values of a flow conclusion lie in the aggregation closure of the
    known values and the active domain. -/
theorem FlowVal.mem_clo {Γ : List (LetDef B ℕ D)} {gd : ℕ → Option (Guards B ℕ D)} {tab : Tab D}
    {W : DB B ℕ D} {n : ℕ} {ss ns : List (Pos B ℕ)} {c : D} (h : FlowVal Γ gd tab W n ss ns c)
    {V : Set D} (hV : known Γ gd tab ∪ adom W ⊆ V) : c ∈ aggClo Γ n V := by
  have hva : ∀ qs, valsOf W qs ⊆ adom W := by
    rintro qs c ⟨q, -, as, has, hc⟩; exact ⟨_, has, List.mem_of_getElem? hc⟩
  rcases h with h | h | h
  · exact aggClo_ext n _ (hV (Or.inl h))
  · exact aggClo_ext n _ (hV (Or.inr (hva ss h)))
  · exact aggClo_mono n (Set.union_subset (fun c hc => hV (Or.inl hc))
      fun c hc => hV (Or.inr (hva ns hc))) h

/-! ## Finiteness of the tables -/

theorem adom_finite' {W : DB B ℕ D} (hW : W.Finite) : (adom W).Finite := by
  have : adom W = ⋃ x ∈ W, {d | d ∈ x.2} := by ext d; simp [adom]
  rw [this]; exact hW.biUnion fun x _ => List.finite_toSet x.2

/-- **Tables stay finite.** -/
theorem tabInv_commit {Γ : List (LetDef B ℕ D)} {v₀ : ℕ → D} {gd : ℕ → Option (Guards B ℕ D)}
    (hord : LetsOrdered Γ) (hg : LetGuards Γ gd) {tab : Tab D} (hinv : TabInv Γ tab) (t : ℕ)
    {W : DB B ℕ D} (hW : W.Finite) : TabInv Γ (commitTab Γ v₀ tab t W) := by
  set V' := aggClo Γ Γ.length (known Γ gd tab ∪ adom W)
  have hV' : V'.Finite := aggClo_finite hg.aggWF _
    (((guardConsts_finite Γ gd).union (tabVals_finite hinv)).union (adom_finite' hW))
  -- new rows of a guardable let are finite
  have hnew : ∀ n (d : LetDef B ℕ D) φ, Γ[n]? = some d → (gd n).isSome →
      d.body.valOp = some φ → (∀ k ω ts ys ψ, d.body ≠ .agg k ω ts ys ψ) →
      {r : ℕ × List D | r.1 = t ∧ r.2.length = d.arity ∧
        sat0 v₀ W (lvOf Γ v₀ tab t W) φ r.2}.Finite := by
    intro n d φ hd hs hvo hna
    obtain ⟨π, hπ⟩ := Option.isSome_iff_exists.1 hs
    have hn : n + 1 ≤ Γ.length := (List.getElem?_eq_some_iff.1 hd).1
    refine ((Set.finite_singleton t).prod (finite_lists V' hV' d.arity)).subset ?_
    rintro ⟨t', as⟩ ⟨ht, hl, hsat⟩
    refine ⟨ht, hl, fun c hc => ?_⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc
    exact aggClo_le hn _ ((row_flow hord hg tab t W n π d φ as hπ hd hvo hna hl hsat i c hi).mem_clo
      le_rfl)
  intro n
  simp only [commitTab]
  rcases hd : Γ[n]? with _ | ⟨ar, body⟩
  · simp
  have htemp := hg.temporal n _ hd
  cases body with
  | since a b φl φr =>
    refine ⟨((hinv n).1.subset fun r hr => hr.1).union
      (hnew n _ φr hd (htemp.1 a b φl φr rfl) rfl (by intros; simp)), Set.finite_empty,
      fun h => ?_⟩
    exact absurd (List.getElem?_eq_some_iff.1 hd).1 (by omega)
  | prev a b φ =>
    exact ⟨Set.finite_empty, hnew n _ φ hd (htemp.2.1 a b φ rfl) rfl (by intros; simp),
      fun h => absurd (List.getElem?_eq_some_iff.1 hd).1 (by omega)⟩
  | now φ => exact ⟨Set.finite_empty, Set.finite_empty, fun h =>
      absurd (List.getElem?_eq_some_iff.1 hd).1 (by omega)⟩
  | agg => exact ⟨Set.finite_empty, Set.finite_empty, fun h =>
      absurd (List.getElem?_eq_some_iff.1 hd).1 (by omega)⟩

/-! ## Well-formed loop parameters from properties of the program -/

theorem DFClause.mono {L : Type} {V V' : Set D} {v₀ : ℕ → D} {ok : L → Prop} {c : Clause B L D}
    (h : DFClause V v₀ ok c) (hV : V ⊆ V') : DFClause V' v₀ ok c :=
  ⟨h.wf, fun t ht d hd => hV (h.consts t ht d hd), h.locals,
    fun t ht x hx hl => hV (h.ctx t ht x hx hl), fun κ hκ a ha t d he => hV (h.eqs κ hκ a ha t d he),
    h.lets⟩

/-- **Well-formed loop parameters.**  The loop with concrete tables and the
    terminating saturation function is well-formed as soon as the input trace
    is, the lets are ordered and guarded (as checked by `TypeLet`), the rules
    satisfy the data-flow criterion with lets decomposed along `lsrcOf`, and
    deferred effects are at least one step ahead. -/
theorem tableParams_wf (Γ : List (LetDef B ℕ D)) (v₀ : ℕ → D) (τ : ℕ → ℕ)
    (inDB : ℕ → DB B ℕ D) (P : Program B ℕ D)
    (hmono : Monotone τ) (hprog : ∀ t, ∃ k, t < τ k) (hfin : ∀ k, (inDB k).Finite)
    (hord : LetsOrdered Γ) (gd : ℕ → Option (Guards B ℕ D)) (hg : LetGuards Γ gd)
    (Vr : Set D) (hVr : Vr.Finite)
    (hrules : ∀ sec ∈ P.secs, ∀ c ∈ sec, DFClause Vr v₀ (fun q => (gd q).isSome) c)
    {Stab : Set D → Set D} (hS : StabOp Stab)
    (hacyc : ∀ sec ∈ P.secs, DFGAcyclic (lsrcOf Γ gd) (nsrcOf Γ gd) Stab sec)
    (hlater : ∀ c ∈ P.rules, ∀ b e ts, c.eff = .later b e ts → 1 ≤ b)
    (hnext : ∀ c ∈ P.rules, ∀ n t e ts, c.eff = .next n t e ts → 1 ≤ n ∧ (t = true → n = 1)) :
    (tableParams Γ v₀ τ inDB P (satFn P.secs)).Wf v₀ where
  mono := hmono
  progress := hprog
  finDB := hfin
  hv₀ _ _ := rfl
  inv₀ n := ⟨Set.finite_empty, Set.finite_empty, fun _ => ⟨rfl, rfl⟩⟩
  invCommit _ t _ hinv hW := tabInv_commit hord hg hinv t hW
  sat tab t D₀ X hinv hD hX := by
    set V := Vr ∪ known Γ gd tab
    have hV : V.Finite := hVr.union ((guardConsts_finite Γ gd).union (tabVals_finite hinv))
    have hA : CloOp (aggClo Γ Γ.length) :=
      ⟨aggClo_ext _, fun _ _ h => aggClo_mono _ h, fun _ hU => aggClo_finite hg.aggWF _ hU⟩
    refine satFn_spec P.secs V hV (lsrcOf Γ gd) (nsrcOf Γ gd) hS hA hacyc
      (fun q => (gd q).isSome) _ ?_
      (fun sec hs c hc => (hrules sec hs c hc).mono Set.subset_union_left) D₀ X hD hX
    intro W p as hp hlv i c hc
    change lvOf Γ v₀ tab t W p as at hlv
    have hpl : p + 1 ≤ Γ.length := by
      rcases hd : Γ[p]? with _ | d
      · simp [lvOf, lvUpTo, hd] at hlv
      · exact (List.getElem?_eq_some_iff.1 hd).1
    rcases lv_flow hord hg tab t W p hp as hlv i c hc with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr (Or.inl h)
    · refine Or.inr (Or.inr (aggClo_le hpl _ (aggClo_mono _ ?_ h)))
      exact Set.union_subset_union Set.subset_union_right le_rfl
  later := hlater
  next := hnext

end Enfflash
