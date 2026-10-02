/-
  The guard atoms of the clauses of `R` name base events or guarded lets.
-/
import Paper.Proof.Levels

namespace Paper

open Classical

variable {Voc : Vocabulary}

theorem GX.names {m : Set Voc.ℰ} {p X Φ π φ} (h : GX m p X Φ π φ) :
    ∀ κ ∈ π, ∀ q ts, GAtom.pred q ts ∈ κ → q ∈ m := by
  induction h with
  | none => intro κ hκ q ts hq; simp at hκ; subst hκ; simp at hq
  | vac => simp
  | pred X p ts hp _ => intro κ hκ q ts' hq; simp at hκ; subst hκ; simp at hq; rw [hq.1]; exact hp
  | eq => intro κ hκ q ts hq; simp at hκ; subst hκ; simp at hq
  | andPos _ _ _ ih₁ ih₂ =>
    intro κ hκ q ts hq
    simp only [GDisj.prod, List.mem_flatMap, List.mem_map] at hκ
    obtain ⟨κ₁, h₁, κ₂, h₂, rfl⟩ := hκ
    rcases List.mem_append.1 hq with hq | hq
    · exact ih₁ κ₁ h₁ q ts hq
    · exact ih₂ κ₂ h₂ q ts hq
  | andNeg _ _ ih₁ ih₂ =>
    intro κ hκ q ts hq
    rcases List.mem_append.1 hκ with hκ | hκ
    · exact ih₁ κ hκ q ts hq
    · exact ih₂ κ hκ q ts hq
  | neg _ ih => exact ih

/-- The guard names of a clause are allowed by `ok`. -/
def GNames (ok : Voc.ℰ → Prop) (c : EClause Voc) : Prop :=
  ∀ κ ∈ c.π, ∀ q ts, GAtom.pred q ts ∈ κ → ok q

theorem gnames_rw {Ξ : RwSetting Voc} {Γ : LetCtx Voc} {ok : Voc.ℰ → Prop}
    (hm : ∀ q ∈ Ξ.m Γ, ok q) (hsup : ∀ e ∈ Ξ.Sup, ok e)
    (hlet : ∀ e g c, Γ e = some (g, c, true) → ok e)
    {α : Mode} {φ : Formula Voc} {𝒞 : CSet Voc} (h : Rw Ξ Γ α φ 𝒞) :
    ∀ C ∈ 𝒞, ∀ c ∈ C, GNames ok c := by
  refine Rw.rec (motive_1 := fun _ _ 𝒞 _ => ∀ C ∈ 𝒞, ∀ c ∈ C, GNames ok c)
    (motive_2 := fun φs 𝒞s _ => List.Forall₂ (fun _ 𝒞 => ∀ C ∈ 𝒞, ∀ c ∈ C, GNames ok c) φs 𝒞s)
    ?top ?evC ?evS ?letC ?letS ?neg ?andS ?andC ?exC ?exS ?futEv ?futNext ?futNextN .nil
    (fun _ _ ih ihs => .cons ih ihs) h
  case top => intro C hC c hc; simp at hC; subst hC; simp at hc
  case evC =>
    intro e ts _ C hC c hc κ hκ q ts' hq
    simp at hC; subst hC; simp at hc; subst hc; simp [GDisj.top] at hκ; subst hκ; simp at hq
  case evS =>
    intro e ts he C hC c hc κ hκ q ts' hq
    simp at hC; subst hC; simp at hc; subst hc; simp at hκ; subst hκ; simp at hq
    rw [hq.1]; exact hsup e he
  case letC =>
    intro e ts _ C hC c hc κ hκ q ts' hq
    simp at hC; subst hC; simp at hc; subst hc; simp [GDisj.top] at hκ; subst hκ; simp at hq
  case letS =>
    intro e ts ⟨g, c', hg⟩ C hC c hc κ hκ q ts' hq
    simp at hC; subst hC; simp at hc; subst hc; simp at hκ; subst hκ; simp at hq
    rw [hq.1]; exact hlet e g c' hg
  case neg => intro _ _ _ _ ih; exact ih
  case andS =>
    intro φs j 𝒞 _ _ _ ih C hC c hc
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    exact ih C₀ hC₀ c₀ hc₀
  case andC =>
    intro φs 𝒞s _ _ ih C hC c hc
    obtain ⟨Cs, hCs, hsub⟩ := mem_bigTensor_eq hC
    obtain ⟨C', hC', hc'⟩ := hsub c hc
    have key : ∀ {φs : List (Formula Voc)} {𝒞s : List (CSet Voc)} {Cs : List (Set (EClause Voc))},
        List.Forall₂ (fun _ 𝒞 => ∀ C ∈ 𝒞, ∀ c ∈ C, GNames ok c) φs 𝒞s →
        List.Forall₂ (· ∈ ·) Cs 𝒞s → ∀ C' ∈ Cs, ∀ c ∈ C', GNames ok c := by
      intro φs 𝒞s Cs h₁ h₂
      induction h₁ generalizing Cs with
      | nil => cases h₂; simp
      | cons hφ _ ih' =>
        cases h₂ with
        | cons hc hcs =>
          intro C' hC'
          rcases List.mem_cons.1 hC' with rfl | hC'
          · exact hφ _ hc
          · exact ih' hcs C' hC'
    exact key ih hCs C' hC' c hc'
  case exC =>
    intro x φ 𝒞 _ hsub ih C hC c hc κ' hκ' q ts hq
    obtain ⟨C₀, hC₀, rfl⟩ := hC
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    obtain ⟨hπ, -⟩ := hsub C₀ hC₀ c₀ hc₀
    obtain ⟨π', hπ'⟩ := Option.isSome_iff_exists.1 hπ
    simp only [hπ', Option.getD_some] at hκ'
    obtain ⟨κ, hκ, hκκ'⟩ := forall₂_mem_right (mapM_forall₂ hπ') κ' hκ'
    obtain ⟨γ, hγ, hγ'⟩ := forall₂_mem_right (mapM_forall₂ hκκ') _ hq
    cases γ with
    | pred p ts'' =>
      simp only [GAtom.subst, Option.some.injEq, GAtom.pred.injEq] at hγ'
      rw [← hγ'.1]; exact ih C₀ hC₀ c₀ hc₀ κ hκ p ts'' hγ
    | eq y c' => simp only [GAtom.subst] at hγ'; split_ifs at hγ'; simp at hγ'
  case exS =>
    intro x φ 𝒞 _ ih C hC c' hc' κ' hκ' q ts hq
    obtain ⟨C₀, hC₀, -, rfl⟩ := hC
    rcases c' with ⟨π', ψ', ε'⟩
    obtain ⟨c, hc, ht, -⟩ := hc'
    simp only at ht hκ'
    cases ht with
    | bound => exact ih C₀ hC₀ c hc κ' hκ' q ts hq
    | @filter π₀ _ hg =>
      simp only [GDisj.prod, List.mem_flatMap, List.mem_map] at hκ'
      obtain ⟨κ, hκ, κ₀, hκ₀, rfl⟩ := hκ'
      rcases List.mem_append.1 hq with hq | hq
      · exact ih C₀ hC₀ c hc κ hκ q ts hq
      · exact hm q (hg.names κ₀ hκ₀ q ts hq)
  case futEv =>
    intro a b h φ 𝒞 _ _ ih C hC c' hc' κ hκ q ts hq
    obtain ⟨C₀, -, rfl⟩ := hC
    obtain ⟨c, -, rfl⟩ := hc'
    simp [GDisj.top] at hκ; subst hκ; simp at hq
  case futNext =>
    intro b φ 𝒞 _ _ ih C hC c' hc' κ hκ q ts hq
    obtain ⟨C₀, -, rfl⟩ := hC
    obtain ⟨c, -, rfl⟩ := hc'
    simp [GDisj.top] at hκ; subst hκ; simp at hq
  case futNextN =>
    intro n φ 𝒞 _ _ ih C hC c' hc' κ hκ q ts hq
    obtain ⟨C₀, -, rfl⟩ := hC
    obtain ⟨c, -, rfl⟩ := hc'
    simp [GDisj.top] at hκ; subst hκ; simp at hq

theorem typeLet_entry {Ξ : RwSetting Voc} {T T' : Typed Voc} {p : Voc.ℰ} {xs : List Voc.𝕍}
    {ψ : Formula Voc} (h : TypeLet Ξ T p xs ψ = some T') :
    (∃ c s, T'.Γ p = some (true, c, s)) ∨ T'.Γ p = some (false, false, false) := by
  unfold TypeLet at h
  generalize stripExists ψ = χ at h
  cases χ with
  | since I φl φr =>
    cases φl <;> simp only at h <;> split_ifs at h <;> cases h <;> simp <;> tauto
  | prev | agg => simp only at h; split_ifs at h; cases h; simp
  | _ => simp only at h; split_ifs at h <;> cases h <;> simp <;> tauto

namespace Setup
variable (U : Setup Voc)

/-- The entries of the final `Γ`. -/
theorem gamma_entry (e : Voc.ℰ) (g c s : Bool) (h : U.T.Γ e = some (g, c, s)) :
    g = true ∨ (g = false ∧ c = false ∧ s = false) := by
  obtain ⟨hnl, -⟩ := typeLets_spec U.lets_body U.wf.nodup U.hT
  by_cases hl : IsLet U.L.lets e
  · obtain ⟨d, hd, rfl⟩ := hl
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    have hlen := TypeLets_take_len U.hT
    obtain ⟨Tk, hTk⟩ := TypeLets_take_isSome U.hT k hk.le
    obtain ⟨Tk1, hTk1⟩ := TypeLets_take_isSome U.hT (k + 1) hk
    have hstep := hTk1
    rw [TypeLets_take_succ k hk, hTk] at hstep
    simp only [Option.bind_some] at hstep
    have hst := TypeLets_take_stable U.wf.nodup k hk U.L.lets.length hk le_rfl Tk1 U.T hTk1 hlen
    rw [hst.1] at h
    rcases typeLet_entry hstep with ⟨c', s', h'⟩ | h'
    · rw [h'] at h; simp at h; exact Or.inl h.1
    · rw [h'] at h; simp at h; exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
  · rw [(hnl e hl).1] at h; simp at h

/-- What a guard may name: a base event or a guarded let. -/
def GOk (q : Voc.ℰ) : Prop := ¬ IsLet U.L.lets q ∨ ∃ c s, U.T.Γ q = some (true, c, s)

theorem prefix_entry {k : ℕ} (hk : k < U.L.lets.length) {Tk : Typed Voc}
    (hTk : TypeLets U.Ξ (U.L.lets.take k) = some Tk) {e : Voc.ℰ}
    (he : (Tk.Γ e).isSome) : Tk.Γ e = U.T.Γ e := by
  obtain ⟨-, hspec⟩ := typeLets_spec U.lets_body U.wf.nodup U.hT
  obtain ⟨Tk', hTk', hpre, -⟩ := hspec k hk
  rw [hTk] at hTk'; cases hTk'
  obtain ⟨k', hk'k, hk', rfl⟩ := hpre e he
  have hlen := TypeLets_take_len U.hT
  obtain ⟨Tk1, hTk1⟩ := TypeLets_take_isSome U.hT (k' + 1) (by omega)
  have h1 := TypeLets_take_stable U.wf.nodup k' hk' k (by omega) hk.le Tk1 Tk hTk1 hTk
  have h2 := TypeLets_take_stable U.wf.nodup k' hk' U.L.lets.length hk' le_rfl Tk1 U.T hTk1 hlen
  rw [h1.1, h2.1]

/-- **The guard atoms of `R`** name base events or guarded lets. -/
theorem R_gnames : ∀ c ∈ U.R, GNames U.GOk c := by
  obtain ⟨-, -, -, hcases⟩ := realization_structure U.hR
  obtain ⟨hnl, hspec⟩ := typeLets_spec U.lets_body U.wf.nodup U.hT
  have hbase : ∀ q ∈ U.Ξ.base, U.GOk q := fun q hq => Or.inl fun ⟨d, hd, he⟩ =>
    (U.wf.fresh_let d hd).2.2.1 (he ▸ hq)
  have hsup : ∀ q ∈ U.Ξ.Sup, U.GOk q := fun q hq => Or.inl fun ⟨d, hd, he⟩ =>
    (U.wf.fresh_let d hd).2.1 (he ▸ hq)
  intro c hc
  rcases hcases c hc with hc | ⟨p, f, hf, hcf⟩ | ⟨p, g, hg, hcg⟩
  · refine gnames_rw (fun q hq => ?_) hsup (fun e g c' h => ?_) U.hrw U.C U.hC c hc
    · rcases hq with hq | ⟨c', s', hq⟩
      · exact hbase q hq
      · exact Or.inr ⟨c', s', hq⟩
    · rcases U.gamma_entry e g c' true h with rfl | ⟨-, -, h'⟩
      · exact Or.inr ⟨c', true, h⟩
      · cases h'
  all_goals
    by_cases hp : IsLet U.L.lets p
    swap
    · first
      | (rw [(hnl p hp).2.1] at hf; exact absurd hf (Set.notMem_empty _))
      | (rw [(hnl p hp).2.2] at hg; exact absurd hg (Set.notMem_empty _))
    obtain ⟨d, hd, rfl⟩ := hp
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hd
    obtain ⟨Tk, hTk0, hTk, -, hCC, hCS⟩ := hspec k hk
    have hm : ∀ q ∈ U.Ξ.m Tk.Γ, U.GOk q := by
      intro q hq
      rcases hq with hq | ⟨c', s', hq⟩
      · exact hbase q hq
      · exact Or.inr ⟨c', s', by rw [← U.prefix_entry hk hTk0 (by simp [hq]), hq]⟩
    have hlt : ∀ e g c', Tk.Γ e = some (g, c', true) → U.GOk e := by
      intro e g c' h
      have h' := (U.prefix_entry hk hTk0 (by simp [h])).symm.trans h
      rcases U.gamma_entry e g c' true h' with rfl | ⟨-, -, h''⟩
      · exact Or.inr ⟨c', true, h'⟩
      · cases h''
    have hobl : ∀ q, (q = U.Ξ.cauN U.L.lets[k].e ∨ q = U.Ξ.supN U.L.lets[k].e) → U.GOk q := by
      rintro q (rfl | rfl)
      · exact Or.inl (U.wf.obl_fresh _ _ (Set.mem_insert _ _)).1
      · exact Or.inl (U.wf.obl_fresh _ _ (Set.mem_insert_of_mem _ rfl)).1
  · obtain ⟨body, 𝒞, C₀, hr, hC₀, rfl, -⟩ := hCC f hf
    obtain ⟨c₀, hc₀, rfl⟩ := hcf
    intro κ' hκ' q ts hq
    simp only [List.mem_map] at hκ'
    obtain ⟨κ, hκ, rfl⟩ := hκ'
    rcases List.mem_append.1 hq with hq | hq
    · exact gnames_rw hm hsup hlt hr C₀ hC₀ c₀ hc₀ κ hκ q ts hq
    · simp at hq; exact hobl q (Or.inl hq.1)
  · obtain ⟨bs, hbs, rfl, -⟩ := hCS g hg
    obtain ⟨c₀, ⟨b, hb, hc₀⟩, rfl⟩ := hcg
    obtain ⟨hr, hC, -⟩ := hbs b hb
    intro κ' hκ' q ts hq
    simp only [List.mem_map] at hκ'
    obtain ⟨κ, hκ, rfl⟩ := hκ'
    rcases List.mem_append.1 hq with hq | hq
    · exact gnames_rw hm hsup hlt hr b.2.2 hC c₀ hc₀ κ hκ q ts hq
    · simp at hq; exact hobl q (Or.inr hq.1)

end Setup

end Paper
