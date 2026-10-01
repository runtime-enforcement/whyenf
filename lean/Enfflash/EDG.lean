/-
  Enfflash formalization — the Event Dependency Graph and section ordering
  (paper, Section 4.5, Figure 7, and Algorithm 4).

  Nodes are event names; there is an edge `e → e'` whenever `e` occurs in the
  trigger of a rule whose effect is on `e'`, let-bound predicates being
  decomposed into the events defining them.  We prove:

  * `stratified_of_topo`: sections in a topological order of the SCCs
    (`SCCOrder`, the sections of `Compile(Γ, R, ≺)`) form a stratified program
    (`Stratified`), as required by `saturate_sound`;
  * `sccOrder_spec`: such an order exists (one section per SCC, by rank);
  * `once_ok`: a section without internal edges may be run `once`.
-/
import Enfflash.Saturate
import Enfflash.Graph
import Mathlib.Data.Set.Finite.Lattice

namespace Enfflash

universe u
variable {B L D : Type u}

/-! ## Syntactic event dependencies -/

section
variable (ld : L → List (Ev B L))

/-- Events occurring in a formula; a let predicate `p` stands for the events
    `ld p` that define it. -/
def Fm.evs : Fm B L D → List (Ev B L)
  | .tt | .eq _ _ => []
  | .pred (.ev e) _ => [e]
  | .pred (.lp p) _ => ld p
  | .neg φ | .ex φ | .ev _ _ φ | .nx _ _ φ => φ.evs
  | .conj φ ψ => φ.evs ++ ψ.evs

def GAtom.evs : GAtom B L D → List (Ev B L)
  | .pred (.ev e) _ => [e]
  | .pred (.lp p) _ => ld p
  | .eq _ _ => []

def Trigger.evs (θ : Trigger B L D) : List (Ev B L) :=
  θ.guards.flatten.flatMap (GAtom.evs ld) ++ θ.filter.evs ld

end

/-- The let interpretation only depends on the events `ld p`. -/
def LetDeps (K : Ctx B L D) (ld : L → List (Ev B L)) : Prop :=
  ∀ W W' : DB B L D, ∀ p, (∀ e ∈ ld p, ∀ as, (e, as) ∈ W ↔ (e, as) ∈ W') → K.lv W p = K.lv W' p

def Agree (W W' : DB B L D) (N : List (Ev B L)) : Prop := ∀ e ∈ N, ∀ as, (e, as) ∈ W ↔ (e, as) ∈ W'

theorem sat_agree {K : Ctx B L D} {ld : L → List (Ev B L)} (hK : LetDeps K ld)
    {W W' : DB B L D} (φ : Fm B L D) (h : Agree W W' (φ.evs ld)) :
    ∀ i w, (ptTr W (K.lv W)).sat i w φ ↔ (ptTr W' (K.lv W')).sat i w φ := by
  induction φ with
  | tt => intros; rfl
  | eq => intros; rfl
  | pred p ts =>
    intro i w
    cases p with
    | ev e => exact h e (by simp [Fm.evs]) _
    | lp p =>
      simp only [Tr.sat, Tr.prIn, ptTr]
      rw [hK W W' p (fun e he as => h e (by simpa [Fm.evs] using he) as)]
  | neg φ ih => intro i w; simp only [Tr.sat]; rw [ih h]
  | ex φ ih => intro i w; simp only [Tr.sat]; exact exists_congr fun d => ih h i _
  | conj φ ψ ih₁ ih₂ =>
    intro i w
    simp only [Tr.sat]
    rw [ih₁ (fun e he => h e (by simp [Fm.evs, he])), ih₂ (fun e he => h e (by simp [Fm.evs, he]))]
  | ev a b φ ih =>
    intro i w
    simp only [Tr.sat, ptTr]
    exact exists_congr fun j => and_congr_right fun _ => and_congr_right fun _ =>
      and_congr_right fun _ => ih h j w
  | nx a b φ ih =>
    intro i w
    simp only [Tr.sat, ptTr]
    exact and_congr_right fun _ => ih h _ w

/-- Syntactic dependencies are semantic dependencies. -/
theorem trigDeps_evs {K : Ctx B L D} {ld : L → List (Ev B L)} (hK : LetDeps K ld)
    (c : Clause B L D) : TrigDeps K c {e | e ∈ c.trig.evs ld} := by
  intro W W' hWW' w
  have hag : ∀ l : List (Ev B L), (∀ e ∈ l, e ∈ c.trig.evs ld) → Agree W W' l :=
    fun l hl e he => hWW' e (hl e he)
  have hg : ∀ a ∈ c.trig.guards.flatten, a.sat (ptTr W (K.lv W)) 0 w ↔
      a.sat (ptTr W' (K.lv W')) 0 w := by
    intro a ha
    have hsub : ∀ e ∈ GAtom.evs ld a, e ∈ c.trig.evs ld := fun e he => by
      simp only [Trigger.evs, List.mem_append, List.mem_flatMap]; exact Or.inl ⟨a, ha, he⟩
    cases a with
    | pred p ts =>
      cases p with
      | ev e => exact hWW' e (hsub e (by simp [GAtom.evs])) _
      | lp p =>
        simp only [GAtom.sat, Tr.prIn, ptTr]
        rw [hK W W' p (fun e he as => hWW' e (hsub e (by simpa [GAtom.evs] using he)) as)]
    | eq => rfl
  have hf := sat_agree hK c.trig.filter
    (hag _ (fun e he => by simp [Trigger.evs, he])) 0 w
  simp only [Trigger.sat, Guards.sat]
  rw [hf]
  refine and_congr_left fun _ => exists_congr fun κ => and_congr_right fun hκ =>
    forall_congr' fun a => forall_congr' fun ha => hg a (List.mem_flatten.2 ⟨κ, hκ, ha⟩)

/-! ## The Event Dependency Graph -/

/-- `e → e'` iff `e` occurs in the trigger of a rule acting on `e'`. -/
def EDG (ld : L → List (Ev B L)) (rules : List (Clause B L D)) (e e' : Ev B L) : Prop :=
  ∃ c ∈ rules, e ∈ c.trig.evs ld ∧ c.eff.name = e'

theorem EDG.finite (ld : L → List (Ev B L)) (rules : List (Clause B L D)) :
    Graph.FiniteGraph (EDG ld rules) := by
  refine ⟨⋃ c ∈ rules, {e | e ∈ c.trig.evs ld ∨ e = c.eff.name},
    Set.Finite.biUnion (List.finite_toSet rules) fun c _ =>
      (List.finite_toSet (c.trig.evs ld)).union (Set.finite_singleton _), ?_⟩
  rintro e e' ⟨c, hc, he, rfl⟩
  exact ⟨Set.mem_biUnion hc (Or.inl he), Set.mem_biUnion hc (Or.inr rfl)⟩

/-! ## Sections from the SCCs of the EDG -/

section
variable (ld : L → List (Ev B L)) (rules : List (Clause B L D))

/-- The SCC rank of the effect of a rule. -/
noncomputable def effRank (c : Clause B L D) : ℕ := Graph.rank (EDG ld rules) c.eff.name

noncomputable def maxRank : ℕ := (rules.map (effRank ld rules)).sum

end

theorem le_sum_of_mem' : ∀ {l : List ℕ} {n : ℕ}, n ∈ l → n ≤ l.sum
  | _ :: l, n, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := le_sum_of_mem' h; simp; omega

/-- A section without internal EDG edges needs a single pass (`once`). -/
theorem once_ok {K : Ctx B L D} {ld : L → List (Ev B L)} (hK : LetDeps K ld)
    (sec : List (Clause B L D)) (h : ∀ c ∈ sec, ∀ c' ∈ sec, c'.eff.name ∉ c.trig.evs ld)
    (D₀ : DB B L D) (X : Set (Act B L D)) : Fixed K D₀ sec (step K D₀ sec X) :=
  once_fixed K D₀ sec X fun c hc => ⟨_, trigDeps_evs hK c, fun c' hc' => h c hc c' hc'⟩

/-! ## Sections in a topological order of the SCCs (Algorithm 4)

`Compile` groups the rules by the SCC of their effect in the EDG and emits
the groups in a topological order `≺` of the SCCs (sources first). -/

open Relation

/-- Sections in topological order of the EDG: no event acted upon in a later
    section reaches an event acted upon in an earlier section. -/
def TopoOrdered (E : Ev B L → Ev B L → Prop) : List (List (Clause B L D)) → Prop
  | [] => True
  | sec :: secs => (∀ c ∈ sec, ∀ s ∈ secs, ∀ c' ∈ s,
      ¬ ReflTransGen E c'.eff.name c.eff.name) ∧ TopoOrdered E secs

/-- The sections of `Compile(Γ, R, ≺)` (Algorithm 4): every rule is in
    some section, the rules of a section act on events of a single SCC of the
    EDG, and the sections follow a topological order `≺` of the SCCs.  (By
    `topo`, the rules of an SCC are never split over two sections.) -/
structure SCCOrder (ld : L → List (Ev B L)) (rules : List (Clause B L D))
    (secs : List (List (Clause B L D))) : Prop where
  cover : ∀ c, c ∈ secs.flatten ↔ c ∈ rules
  scc : ∀ sec ∈ secs, ∀ c ∈ sec, ∀ c' ∈ sec,
    ReflTransGen (EDG ld rules) c.eff.name c'.eff.name
  topo : TopoOrdered (EDG ld rules) secs

/-- **Section order.**  Sections in a topological order of the EDG are
    stratified. -/
theorem stratified_of_topo {K : Ctx B L D} {ld : L → List (Ev B L)} (hK : LetDeps K ld)
    (rules : List (Clause B L D)) :
    ∀ (secs : List (List (Clause B L D))), (∀ sec ∈ secs, ∀ c ∈ sec, c ∈ rules) →
      TopoOrdered (EDG ld rules) secs → Stratified K secs
  | [], _, _ => trivial
  | sec :: secs, hsub, ⟨hord, hrest⟩ =>
    ⟨fun c hc => ⟨_, trigDeps_evs hK c, fun s hs c' hc' hin =>
        hord c hc s hs c' hc'
          (ReflTransGen.single ⟨c, hsub sec (List.mem_cons_self ..) c hc, hin, rfl⟩)⟩,
     stratified_of_topo hK rules secs (fun s hs => hsub s (List.mem_cons_of_mem _ hs)) hrest⟩

theorem TopoOrdered.append {E : Ev B L → Ev B L → Prop} :
    ∀ {l₁ l₂ : List (List (Clause B L D))}, TopoOrdered E l₁ → TopoOrdered E l₂ →
      (∀ A ∈ l₁, ∀ B ∈ l₂, ∀ c ∈ A, ∀ c' ∈ B, ¬ ReflTransGen E c'.eff.name c.eff.name) →
      TopoOrdered E (l₁ ++ l₂)
  | [], _, _, h₂, _ => h₂
  | A :: l₁, l₂, ⟨hA, h₁⟩, h₂, hx => by
    refine ⟨fun c hc s hs c' hc' => ?_,
      TopoOrdered.append h₁ h₂ fun A' hA' => hx A' (List.mem_cons_of_mem _ hA')⟩
    rcases List.mem_append.1 hs with hs | hs
    · exact hA c hc s hs c' hc'
    · exact hx A (List.mem_cons_self ..) s hs c hc c' hc'

theorem TopoOrdered.of_pairwise {E : Ev B L → Ev B L → Prop} :
    ∀ {l : List (List (Clause B L D))}, l.Nodup →
      (∀ A ∈ l, ∀ B ∈ l, A ≠ B → ∀ c ∈ A, ∀ c' ∈ B, ¬ ReflTransGen E c'.eff.name c.eff.name) →
      TopoOrdered E l
  | [], _, _ => trivial
  | A :: l, hnd, h => by
    rw [List.nodup_cons] at hnd
    refine ⟨fun c hc s hs c' hc' => h A (List.mem_cons_self ..) s (List.mem_cons_of_mem _ hs)
      (fun he => hnd.1 (he ▸ hs)) c hc c' hc',
      TopoOrdered.of_pairwise hnd.2 fun A' hA' B' hB' => h A' (List.mem_cons_of_mem _ hA')
        B' (List.mem_cons_of_mem _ hB')⟩

/-! ### Existence of an SCC order -/

section
variable (ld : L → List (Ev B L)) (rules : List (Clause B L D))

open Classical

/-- The effects of two rules lie in the same SCC. -/
def sameSCC (c c' : Clause B L D) : Prop :=
  ReflTransGen (EDG ld rules) c.eff.name c'.eff.name ∧
    ReflTransGen (EDG ld rules) c'.eff.name c.eff.name

noncomputable def rankRules (r : ℕ) : List (Clause B L D) :=
  rules.filter (fun c => decide (effRank ld rules c = r))

/-- The rules of rank `r` in the SCC of `c`. -/
noncomputable def sccClass (r : ℕ) (c : Clause B L D) : List (Clause B L D) :=
  (rankRules ld rules r).filter (fun c' => decide (sameSCC ld rules c c'))

/-- The SCCs of rank `r` (in any order: they are pairwise unrelated). -/
noncomputable def classesAt (r : ℕ) : List (List (Clause B L D)) :=
  ((rankRules ld rules r).map (sccClass ld rules r)).dedup

/-- One section per SCC, by increasing rank. -/
noncomputable def sccOrder : List (List (Clause B L D)) :=
  (List.range (maxRank ld rules + 1)).flatMap (classesAt ld rules)

end

theorem mem_classesAt {ld : L → List (Ev B L)} {rules : List (Clause B L D)} {r : ℕ}
    {A : List (Clause B L D)} (h : A ∈ classesAt ld rules r) :
    ∃ a ∈ rankRules ld rules r, A = sccClass ld rules r a := by
  classical
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 h)
  exact ⟨a, ha, rfl⟩

theorem mem_sccClass {ld : L → List (Ev B L)} {rules : List (Clause B L D)} {r : ℕ}
    {a c : Clause B L D} (h : c ∈ sccClass ld rules r a) :
    c ∈ rules ∧ effRank ld rules c = r ∧ sameSCC ld rules a c := by
  classical
  simp only [sccClass, rankRules, List.mem_filter, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **An SCC order exists** (as computed by the compiler with Tarjan's
    algorithm). -/
theorem sccOrder_spec (ld : L → List (Ev B L)) (rules : List (Clause B L D)) :
    SCCOrder ld rules (sccOrder ld rules) := by
  classical
  have hE := EDG.finite ld rules
  have hmem : ∀ A ∈ sccOrder ld rules, ∃ r a, a ∈ rankRules ld rules r ∧
      A = sccClass ld rules r a := by
    intro A hA
    obtain ⟨r, -, hA⟩ := List.mem_flatMap.1 hA
    obtain ⟨a, ha, rfl⟩ := mem_classesAt hA
    exact ⟨r, a, ha, rfl⟩
  refine ⟨fun c => ⟨fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · obtain ⟨A, hA, hc⟩ := List.mem_flatten.1 h
    obtain ⟨r, a, -, rfl⟩ := hmem A hA
    exact (mem_sccClass hc).1
  · have hle : effRank ld rules c ≤ maxRank ld rules :=
      le_sum_of_mem' (List.mem_map_of_mem h)
    have hcr : c ∈ rankRules ld rules (effRank ld rules c) := by
      simp [rankRules, h]
    refine List.mem_flatten.2 ⟨sccClass ld rules (effRank ld rules c) c,
      List.mem_flatMap.2 ⟨effRank ld rules c, List.mem_range.2 (by omega),
        List.mem_dedup.2 (List.mem_map_of_mem hcr)⟩, ?_⟩
    simp only [sccClass, List.mem_filter, decide_eq_true_eq]
    exact ⟨hcr, ReflTransGen.refl, ReflTransGen.refl⟩
  · intro A hA c hc c' hc'
    obtain ⟨r, a, -, rfl⟩ := hmem A hA
    exact (mem_sccClass hc).2.2.2.trans (mem_sccClass hc').2.2.1
  · -- ranks increase along the list, and classes of equal rank are unrelated
    have hrank : ∀ r, ∀ A ∈ classesAt ld rules r, ∀ c ∈ A, effRank ld rules c = r := by
      intro r A hA c hc
      obtain ⟨a, -, rfl⟩ := mem_classesAt hA
      exact (mem_sccClass hc).2.1
    have hsame : ∀ r, TopoOrdered (EDG ld rules) (classesAt ld rules r) := by
      intro r
      refine TopoOrdered.of_pairwise (List.nodup_dedup _) ?_
      intro A hA B hB hAB c hc c' hc' hpath
      obtain ⟨a, -, rfl⟩ := mem_classesAt hA
      obtain ⟨b, -, rfl⟩ := mem_classesAt hB
      obtain ⟨-, hcr, hac⟩ := mem_sccClass hc
      obtain ⟨-, hcr', hbc'⟩ := mem_sccClass hc'
      have hback := Graph.rank_eq_path hE hpath (by
        simp only [effRank] at hcr hcr'; rw [hcr, hcr'])
      have hab : sameSCC ld rules a b :=
        ⟨hac.1.trans (hback.trans hbc'.2), hbc'.1.trans (hpath.trans hac.2)⟩
      apply hAB
      simp only [sccClass]
      apply List.filter_congr
      intro x _
      simp only [sameSCC, decide_eq_decide]
      exact ⟨fun h => ⟨hab.2.trans h.1, h.2.trans hab.1⟩,
        fun h => ⟨hab.1.trans h.1, h.2.trans hab.2⟩⟩
    have key : ∀ rs : List ℕ, rs.Pairwise (· < ·) →
        TopoOrdered (EDG ld rules) (rs.flatMap (classesAt ld rules)) := by
      intro rs
      induction rs with
      | nil => intro; trivial
      | cons r rs ih =>
        intro hp
        rw [List.pairwise_cons] at hp
        rw [List.flatMap_cons]
        refine TopoOrdered.append (hsame r) (ih hp.2) ?_
        intro A hA B hB c hc c' hc' hpath
        obtain ⟨r', hr', hB⟩ := List.mem_flatMap.1 hB
        have h1 := hrank r A hA c hc
        have h2 := hrank r' B hB c' hc'
        have h3 := Graph.rank_mono_path hE hpath
        have h4 := hp.1 r' hr'
        simp only [effRank] at h1 h2
        omega
    exact key _ (List.pairwise_lt_range)

end Enfflash
