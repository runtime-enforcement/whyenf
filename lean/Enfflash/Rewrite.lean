/-
  EnfFlash formalization — enforcement rewriting (paper, Section 4.3,
  Figure 6) and its local soundness.

  `Rw S true φ CS`  : every clause set `C ∈ CS` *causes* `φ`;
  `Rw S false φ CS` : every clause set `C ∈ CS` *suppresses* `φ`.

  Local soundness (`Rw.sound`): at any time-point of any trace where all
  clauses of `C` hold, `φ` holds (resp. fails).
-/
import Enfflash.Guards

namespace Enfflash

universe u
variable {B L D : Type u}

/-! ## Causation and suppression targets of let bodies -/

namespace LBody

/-- The formula whose causation causes the let (`TypeLet`, causation part). -/
def cauTarget : LBody B L D → Option (Fm B L D)
  | now φ => some φ
  | since a _ _ φr => if a = 0 then some φr else none
  | _ => none

/-- The formula whose suppression suppresses the let.  For `φl S_[a,b] φr`
    with `a > 0` this is the *left* operand: the witness of the since lies
    strictly in the past, so only falsifying `φl` now can falsify it.  (The
    paper's Algorithm 3 and the original compiler used `φr` here, which is
    unsound.) -/
def supTarget : LBody B L D → Option (Fm B L D)
  | now φ => some φ
  | since a _ φl φr => if a = 0 then some (Fm.disj φl φr) else some φl
  | _ => none

theorem cauTarget_sound (σ : Tr B L D) (i : ℕ) (w : ℕ → D) {body : LBody B L D}
    {φ : Fm B L D} (h : body.cauTarget = some φ) (hφ : σ.sat i w φ) : body.sem σ i w := by
  cases body with
  | now ψ => cases h; exact hφ
  | since a b φl φr =>
    simp only [cauTarget] at h
    split_ifs at h with ha
    cases h
    exact ⟨i, le_rfl, ⟨by omega, fun b' _ => by omega⟩, hφ, fun k h1 h2 => absurd h2 (by omega)⟩
  | prev => cases h
  | agg => cases h

theorem supTarget_sound (σ : Tr B L D) (i : ℕ) (w : ℕ → D) {body : LBody B L D}
    {φ : Fm B L D} (h : body.supTarget = some φ) (hφ : ¬ σ.sat i w φ) : ¬ body.sem σ i w := by
  cases body with
  | now ψ => cases h; exact hφ
  | since a b φl φr =>
    simp only [supTarget] at h
    rintro ⟨j, hj, hI, hr, hl⟩
    split_ifs at h with ha
    · cases h
      rw [Tr.sat_disj] at hφ
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact hφ (Or.inl (hl i hj le_rfl))
      · exact hφ (Or.inr hr)
    · cases h
      rcases Nat.lt_or_eq_of_le hj with hj | rfl
      · exact hφ (hl i hj le_rfl)
      · have := hI.1; simp at this; omega
  | prev => cases h
  | agg => cases h

end LBody

/-! ## The rewriting judgement -/

/-- Parameters of the rewriting: the enforcement signature (causable and
    suppressable base events), enumerable predicates for guards, let arities,
    the lets that are causable / suppressable in the current scope, and the
    canonical witness `d₀` used to cause existentials (the paper's `0`). -/
structure Sig (B L D : Type u) where
  cau : B → Prop
  sup : B → Prop
  enum : Pr B L → Prop
  ar : L → ℕ
  okC : L → Prop
  okS : L → Prop
  d₀ : D

namespace Clause

/-- `⊤ ⇒ e(t̄)` with no local variables. -/
def simple (c : Clause B L D) : Prop :=
  c.nloc = 0 ∧ c.trig = Trigger.top ∧ ∃ e ts, c.eff = .cau e ts

def mapCau (f : Ev B L → List (Term D) → Effect B L D) (c : Clause B L D) : Clause B L D :=
  match c.eff with
  | .cau e ts => ⟨c.nloc, c.trig, f e ts⟩
  | _ => c

/-- Conjoin a (context) formula to the filter. -/
def addFilter (ψ : Fm B L D) (c : Clause B L D) : Clause B L D :=
  ⟨c.nloc, c.trig.andFilter (ψ.subst (liftS c.nloc)), c.eff⟩

end Clause

def prodCS (CS₁ CS₂ : List (List (Clause B L D))) : List (List (Clause B L D)) :=
  CS₁.flatMap (fun C₁ => CS₂.map (fun C₂ => C₁ ++ C₂))

/-- `○ … ○ φ` (`n` unbounded nexts). -/
def nxU : ℕ → Fm B L D → Fm B L D
  | 0, φ => φ
  | n + 1, φ => .nx 0 none (nxU n φ)

/-- Guard extraction for the variable bound by an existential (rule `Ex^S`). -/
def ExGuard (m : Pr B L → Prop) (c c' : Clause B L D) : Prop :=
  c'.nloc = c.nloc + 1 ∧ c'.eff = c.eff ∧
    GX m c.nloc true c.trig.guards c.trig.filter c'.trig.guards c'.trig.filter

/-- The enforcement rewrite rules (Figure 6). -/
inductive Rw (S : Sig B L D) : Bool → Fm B L D → List (List (Clause B L D)) → Prop
  | tt : Rw S true .tt [[]]
  | evC {e ts} : S.cau e →
      Rw S true (.pred (.ev (.base e)) ts) [[⟨0, Trigger.top, .cau (.base e) ts⟩]]
  | evS {e ts} : S.sup e →
      Rw S false (.pred (.ev (.base e)) ts)
        [[⟨0, ⟨[[.pred (.ev (.base e)) ts]], .tt⟩, .sup (.base e) ts⟩]]
  | letC {p ts} : S.okC p → ts.length = S.ar p →
      Rw S true (.pred (.lp p) ts) [[⟨0, Trigger.top, .cau (.cau p) ts⟩]]
  | letS {p ts} : S.okS p → ts.length = S.ar p →
      Rw S false (.pred (.lp p) ts) [[⟨0, ⟨[[.pred (.lp p) ts]], .tt⟩, .cau (.sup p) ts⟩]]
  | neg {pol φ CS} : Rw S (!pol) φ CS → Rw S pol (.neg φ) CS
  | andC {φ ψ CS₁ CS₂} : Rw S true φ CS₁ → Rw S true ψ CS₂ →
      Rw S true (.conj φ ψ) (prodCS CS₁ CS₂)
  | andSL {φ ψ CS} : Rw S false φ CS → ψ.present →
      Rw S false (.conj φ ψ) (CS.map (List.map (Clause.addFilter ψ)))
  | andSR {φ ψ CS} : Rw S false ψ CS → φ.present →
      Rw S false (.conj φ ψ) (CS.map (List.map (Clause.addFilter φ)))
  | exC {φ CS} : Rw S true φ CS →
      Rw S true (.ex φ) (CS.map (List.map (Clause.substCtx (instS 0 S.d₀))))
  | exS {φ CS CS'} : Rw S false φ CS →
      (∀ C' ∈ CS', ∃ C ∈ CS, List.Forall₂ (ExGuard S.enum) C C') →
      Rw S false (.ex φ) CS'
  | futEv {a b φ CS CS'} : Rw S true φ CS → a ≤ b → 1 ≤ b →
      (∀ C' ∈ CS', ∃ C ∈ CS, C ≠ [] ∧ (∀ c ∈ C, c.simple) ∧
        C' = C.map (Clause.mapCau (.later b))) →
      Rw S true (.ev a b φ) CS'
  | futNx1 {b φ CS CS'} : Rw S true φ CS → 1 ≤ b →
      (∀ C' ∈ CS', ∃ C ∈ CS, C ≠ [] ∧ (∀ c ∈ C, c.simple) ∧
        C' = C.map (Clause.mapCau (.next 1 true))) →
      Rw S true (.nx 0 (some b) φ) CS'
  | futNxU {n φ CS CS'} : Rw S true φ CS → 1 ≤ n →
      (∀ C' ∈ CS', ∃ C ∈ CS, (∀ c ∈ C, c.simple) ∧
        C' = C.map (Clause.mapCau (.next n false))) →
      Rw S true (nxU n φ) CS'

/-! ## Local soundness -/

/-- Whenever the obligation event `Cau_p(ā)` is present, `p(ā)` holds. -/
def CauOK (σ : Tr B L D) (ar : L → ℕ) (p : L) : Prop :=
  ∀ i (as : List D), as.length = ar p → (Ev.cau p, as) ∈ σ.db i → σ.lv i p as

/-- Whenever the obligation event `Sup_p(ā)` is present, `p(ā)` fails. -/
def SupOK (σ : Tr B L D) (ar : L → ℕ) (p : L) : Prop :=
  ∀ i (as : List D), as.length = ar p → (Ev.sup p, as) ∈ σ.db i → ¬ σ.lv i p as

def polSem (pol : Bool) (P : Prop) : Prop := if pol then P else ¬ P

theorem lastAt_unique {σ : Tr B L D} (hm : Monotone σ.ts) {t j j' : ℕ}
    (h : Effect.lastAt σ t j) (h' : Effect.lastAt σ t j') : j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · have := hm (show j + 1 ≤ j' by omega); rw [h'.1] at this; exact absurd h.2 (by omega)
  · exact heq
  · have := hm (show j' + 1 ≤ j by omega); rw [h.1] at this; exact absurd h'.2 (by omega)

theorem lastAt_ge {σ : Tr B L D} (hm : Monotone σ.ts) {i b j : ℕ}
    (h : Effect.lastAt σ (σ.ts i + b) j) : i ≤ j := by
  by_contra hc
  have := hm (show j + 1 ≤ i by omega)
  exact absurd h.2 (by omega)

theorem sat_nxU (σ : Tr B L D) (v : ℕ → D) (φ : Fm B L D) :
    ∀ (n i : ℕ), σ.sat (i + n) v φ → σ.sat i v (nxU n φ)
  | 0, i, h => h
  | n + 1, i, h => ⟨⟨Nat.zero_le _, fun _ h => by cases h⟩,
      sat_nxU σ v φ n (i + 1) (by rwa [show i + 1 + n = i + (n + 1) by omega])⟩

theorem simple_holds_iff {σ : Tr B L D} {i : ℕ} {v : ℕ → D} {c : Clause B L D}
    (hc : c.simple) {e : Ev B L} {ts : List (Term D)} (he : c.eff = .cau e ts) :
    c.holds σ i v ↔ (e, ts.map (Term.eval v)) ∈ σ.db i := by
  obtain ⟨h0, htop, -⟩ := hc
  constructor
  · intro h
    have := h [] (by simp [h0]) (by rw [htop]; exact ⟨Guards.sat_top σ i v, trivial⟩)
    rwa [he] at this
  · intro h ds hds _
    have : ds = [] := List.eq_nil_of_length_eq_zero (hds.trans h0)
    subst this; rw [he]; exact h

theorem forall₂_left {α β : Type u} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a}, a ∈ l₁ → ∃ b ∈ l₂, R a b
  | _, _, .nil, _, h => by simp at h
  | _, _, .cons hr hrest, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self .., hr⟩
    · obtain ⟨b, hb, hab⟩ := forall₂_left hrest h
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

/-- **Local soundness of the enforcement rewriting.**  If all clauses of an
    alternative `C` hold at time-point `i`, then `φ` is caused (`pol = true`)
    resp. suppressed (`pol = false`) at `i`. -/
theorem Rw.sound {S : Sig B L D} {σ : Tr B L D} (hm : Monotone σ.ts)
    (hC : ∀ p, S.okC p → CauOK σ S.ar p) (hS : ∀ p, S.okS p → SupOK σ S.ar p)
    {pol : Bool} {φ : Fm B L D} {CS : List (List (Clause B L D))} (h : Rw S pol φ CS) :
    ∀ C ∈ CS, ∀ i v, Clauses.holds σ i v C → polSem pol (σ.sat i v φ) := by
  induction h with
  | tt => intros; simp [polSem, Tr.sat]
  | evC =>
    intro C hC' i v hh
    simp only [List.mem_singleton] at hC'; subst hC'
    have := hh _ (List.mem_singleton_self _) [] rfl ⟨Guards.sat_top σ i v, trivial⟩
    simpa [polSem, Tr.sat, Tr.prIn, Effect.holds] using this
  | evS =>
    intro C hC' i v hh
    simp only [List.mem_singleton] at hC'; subst hC'
    simp only [polSem, Bool.false_eq_true, if_false, Tr.sat, Tr.prIn]
    intro hin
    have := hh _ (List.mem_singleton_self _) [] rfl ⟨⟨_, List.mem_singleton_self _, by simpa [GAtom.sat, Tr.prIn]⟩,
      trivial⟩
    exact this (by simpa using hin)
  | @letC p ts hok hlen =>
    intro C hC' i v hh
    simp only [List.mem_singleton] at hC'; subst hC'
    have := hh _ (List.mem_singleton_self _) [] rfl ⟨Guards.sat_top σ i v, trivial⟩
    simp only [Effect.holds, vapp_nil] at this
    simp only [polSem, if_true, Tr.sat, Tr.prIn]
    exact hC p hok i _ (by simp [hlen]) this
  | @letS p ts hok hlen =>
    intro C hC' i v hh
    simp only [List.mem_singleton] at hC'; subst hC'
    simp only [polSem, Bool.false_eq_true, if_false, Tr.sat, Tr.prIn]
    intro hin
    have := hh _ (List.mem_singleton_self _) [] rfl ⟨⟨_, List.mem_singleton_self _, by simpa [GAtom.sat, Tr.prIn]⟩,
      trivial⟩
    simp only [Effect.holds, vapp_nil] at this
    exact hS p hok i _ (by simp [hlen]) this hin
  | @neg pol φ CS _ ih =>
    intro C hC' i v hh
    have := ih C hC' i v hh
    cases pol <;> simp_all [polSem, Tr.sat]
  | andC _ _ ih₁ ih₂ =>
    intro C hC' i v hh
    simp only [prodCS, List.mem_flatMap, List.mem_map] at hC'
    obtain ⟨C₁, h₁, C₂, h₂, rfl⟩ := hC'
    have a := ih₁ C₁ h₁ i v (fun c hc => hh c (List.mem_append_left _ hc))
    have b := ih₂ C₂ h₂ i v (fun c hc => hh c (List.mem_append_right _ hc))
    simp only [polSem, if_true] at a b ⊢
    exact ⟨a, b⟩
  | @andSL φ ψ CS _ _ ih =>
    intro C hC' i v hh
    obtain ⟨C₀, h₀, rfl⟩ := List.mem_map.1 hC'
    simp only [polSem, Bool.false_eq_true, if_false, Tr.sat]
    rintro ⟨hφ, hψ⟩
    have hC0 : Clauses.holds σ i v C₀ := by
      intro c hc ds hds htr
      apply hh _ (List.mem_map_of_mem hc) ds hds
      refine ⟨htr.1, htr.2, ?_⟩
      rw [Tr.sat_subst, ← hds, eval_liftS]; exact hψ
    exact (show ¬ σ.sat i v φ by simpa [polSem] using ih C₀ h₀ i v hC0) hφ
  | @andSR φ ψ CS _ _ ih =>
    intro C hC' i v hh
    obtain ⟨C₀, h₀, rfl⟩ := List.mem_map.1 hC'
    simp only [polSem, Bool.false_eq_true, if_false, Tr.sat]
    rintro ⟨hφ, hψ⟩
    have hC0 : Clauses.holds σ i v C₀ := by
      intro c hc ds hds htr
      apply hh _ (List.mem_map_of_mem hc) ds hds
      refine ⟨htr.1, htr.2, ?_⟩
      rw [Tr.sat_subst, ← hds, eval_liftS]; exact hφ
    exact (show ¬ σ.sat i v ψ by simpa [polSem] using ih C₀ h₀ i v hC0) hψ
  | exC _ ih =>
    intro C hC' i v hh
    obtain ⟨C₀, h₀, rfl⟩ := List.mem_map.1 hC'
    have key : (fun n => (instS 0 S.d₀ n).eval v) = vcons S.d₀ v := by
      simpa using eval_instS ([] : List D) S.d₀ v
    have := ih C₀ h₀ i (vcons S.d₀ v) (fun c hc => by
      rw [← key, ← Clause.holds_substCtx]; exact hh _ (List.mem_map_of_mem hc))
    simp only [polSem, if_true, Tr.sat] at this ⊢
    exact ⟨_, this⟩
  | @exS φ CS CS' _ hCS ih =>
    intro C' hC' i v hh
    obtain ⟨C, hC, h2⟩ := hCS C' hC'
    simp only [polSem, Bool.false_eq_true, if_false, Tr.sat, not_exists]
    intro d
    suffices hCd : Clauses.holds σ i (vcons d v) C by
      simpa [polSem] using ih C hC i (vcons d v) hCd
    intro c hc
    obtain ⟨c', hc', hg⟩ := forall₂_left h2 hc
    obtain ⟨hn, he, hgx⟩ := hg
    intro ds hds htr
    have hc'h := hh c' hc' (ds ++ [d]) (by simp [hn, hds])
    rw [vapp_append] at hc'h
    have eqv := (hgx.sound.1 σ i (vapp ds (vapp [d] v))).1
    simp only [polSat, if_true] at eqv
    have := hc'h (eqv htr)
    rw [he] at this; simpa using this
  | @futEv a b φ CS CS' _ hab hb hCS ih =>
    intro C' hC' i v hh
    obtain ⟨C, hC, hne, hsimp, rfl⟩ := hCS C' hC'
    obtain ⟨c₀, hc₀⟩ := List.exists_mem_of_ne_nil C hne
    -- the (unique) proactive time-point for timestamp `ts i + b`
    have hlater : ∀ c ∈ C, ∀ e ts, c.eff = .cau e ts →
        ∃ j, Effect.lastAt σ (σ.ts i + b) j ∧ (e, ts.map (Term.eval v)) ∈ σ.db j := by
      intro c hc e ts he
      obtain ⟨h0, htop, -⟩ := hsimp c hc
      have := hh _ (List.mem_map_of_mem hc) [] (by simp [Clause.mapCau, he, h0])
        (by simp only [Clause.mapCau, he, htop]; exact ⟨Guards.sat_top σ i _, trivial⟩)
      simpa [Clause.mapCau, he, Effect.holds] using this
    obtain ⟨e₀, ts₀, he₀⟩ := (hsimp c₀ hc₀).2.2
    obtain ⟨j, hj, -⟩ := hlater c₀ hc₀ e₀ ts₀ he₀
    have hCj : Clauses.holds σ j v C := by
      intro c hc
      obtain ⟨e, ts, he⟩ := (hsimp c hc).2.2
      rw [simple_holds_iff (hsimp c hc) he]
      obtain ⟨j', hj', hin⟩ := hlater c hc e ts he
      rwa [lastAt_unique hm hj hj']
    have := ih C hC j v hCj
    simp only [polSem, if_true, Tr.sat] at this ⊢
    refine ⟨j, lastAt_ge hm hj, ?_, ?_, this⟩ <;> rw [hj.1] <;> omega
  | @futNx1 b φ CS CS' _ hb hCS ih =>
    intro C' hC' i v hh
    obtain ⟨C, hC, hne, hsimp, rfl⟩ := hCS C' hC'
    obtain ⟨c₀, hc₀⟩ := List.exists_mem_of_ne_nil C hne
    have hnext : ∀ c ∈ C, ∀ e ts, c.eff = .cau e ts →
        (σ.ts (i + 1) ≤ σ.ts i + 1) ∧ (e, ts.map (Term.eval v)) ∈ σ.db (i + 1) := by
      intro c hc e ts he
      obtain ⟨h0, htop, -⟩ := hsimp c hc
      have := hh _ (List.mem_map_of_mem hc) [] (by simp [Clause.mapCau, he, h0])
        (by simp only [Clause.mapCau, he, htop]; exact ⟨Guards.sat_top σ i _, trivial⟩)
      simpa [Clause.mapCau, he, Effect.holds] using this
    obtain ⟨e₀, ts₀, he₀⟩ := (hsimp c₀ hc₀).2.2
    have hCj : Clauses.holds σ (i + 1) v C := by
      intro c hc
      obtain ⟨e, ts, he⟩ := (hsimp c hc).2.2
      rw [simple_holds_iff (hsimp c hc) he]
      exact (hnext c hc e ts he).2
    have := ih C hC _ v hCj
    have ht := (hnext c₀ hc₀ e₀ ts₀ he₀).1
    simp only [polSem, if_true, Tr.sat, inI] at this ⊢
    refine ⟨⟨Nat.zero_le _, fun b' hb' => ?_⟩, this⟩
    cases hb'; omega
  | @futNxU n φ CS CS' _ _ hCS ih =>
    intro C' hC' i v hh
    obtain ⟨C, hC, hsimp, rfl⟩ := hCS C' hC'
    have hCj : Clauses.holds σ (i + n) v C := by
      intro c hc
      obtain ⟨e, ts, he⟩ := (hsimp c hc).2.2
      rw [simple_holds_iff (hsimp c hc) he]
      obtain ⟨h0, htop, -⟩ := hsimp c hc
      have := hh _ (List.mem_map_of_mem hc) [] (by simp [Clause.mapCau, he, h0])
        (by simp only [Clause.mapCau, he, htop]; exact ⟨Guards.sat_top σ i _, trivial⟩)
      simpa [Clause.mapCau, he, Effect.holds] using this
    have := ih C hC _ v hCj
    simp only [polSem, if_true] at this ⊢
    exact sat_nxU σ v φ n i this

end Enfflash
