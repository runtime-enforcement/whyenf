(*<*)
theory Proof_System
  imports Formula "HOL-Library.Disjoint_Sets" (*"Deriving.Comparator_Generator"*) (*"Containers.Collection_Order" "Containers.Set_Impl"*)
begin
(*>*)

context begin

section \<open>Proof System\<close>

subsection \<open>Time-stamp-time-point Conversion\<close>

definition ETP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat"  where
  "ETP \<sigma> t = (LEAST i. \<tau> \<sigma> i \<ge> t)"

definition LTP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat" where
  "LTP \<sigma> t = Max {i. (\<tau> \<sigma> i) \<le> t}"

abbreviation "\<delta> \<sigma> i j \<equiv> (\<tau> \<sigma> i - \<tau> \<sigma> j)"

abbreviation "ETP_p \<sigma> i b \<equiv> ETP \<sigma> ((\<tau> \<sigma> i) - b)"
abbreviation "LTP_p \<sigma> i I \<equiv> min i (LTP \<sigma> ((\<tau> \<sigma> i) - left I))"
abbreviation "ETP_f \<sigma> i I \<equiv> max i (ETP \<sigma> ((\<tau> \<sigma> i) + left I))"
abbreviation "LTP_f \<sigma> i b \<equiv> LTP \<sigma> ((\<tau> \<sigma> i) + b)"

definition max_opt where
  "max_opt a b = (case (a,b) of (Some x, Some y) \<Rightarrow> Some (max x y) | _ \<Rightarrow> None)"

definition "LTP_p_safe \<sigma> i I = (if \<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> 0 then LTP_p \<sigma> i I else 0)"

(* Latest Relevant Time-Point *)
fun LRTP :: "'a Formula.trace \<Rightarrow> 'a Formula.formula \<Rightarrow> nat \<Rightarrow> nat option" where
  "LRTP \<sigma> (Formula.TT) i = Some i"
| "LRTP \<sigma> (Formula.FF) i = Some i"
| "LRTP \<sigma> (Formula.Pred _ _) i = Some i"
| "LRTP \<sigma> (Formula.Eq_Const _ _) i = Some i"
| "LRTP \<sigma> (Formula.Neg \<phi>) i = LRTP \<sigma> \<phi> i"
| "LRTP \<sigma> (Formula.Or \<phi> \<psi>) i = max_opt (LRTP \<sigma> \<phi> i) (LRTP \<sigma> \<psi> i)"
| "LRTP \<sigma> (Formula.And \<phi> \<psi>) i = max_opt (LRTP \<sigma> \<phi> i) (LRTP \<sigma> \<psi> i)"
| "LRTP \<sigma> (Formula.Imp \<phi> \<psi>) i = max_opt (LRTP \<sigma> \<phi> i) (LRTP \<sigma> \<psi> i)"
| "LRTP \<sigma> (Formula.Iff \<phi> \<psi>) i = max_opt (LRTP \<sigma> \<phi> i) (LRTP \<sigma> \<psi> i)"
| "LRTP \<sigma> (Formula.Exists _ \<phi>) i = LRTP \<sigma> \<phi> i"
| "LRTP \<sigma> (Formula.Forall _ \<phi>) i = LRTP \<sigma> \<phi> i"
| "LRTP \<sigma> (Formula.Prev I \<phi>) i = LRTP \<sigma> \<phi> (i-1)"
| "LRTP \<sigma> (Formula.Next I \<phi>) i = LRTP \<sigma> \<phi> (i+1)"
| "LRTP \<sigma> (Formula.Once I \<phi>) i = LRTP \<sigma> \<phi> (LTP_p_safe \<sigma> i I)"
| "LRTP \<sigma> (Formula.Historically I \<phi>) i = LRTP \<sigma> \<phi> (LTP_p_safe \<sigma> i I)"
| "LRTP \<sigma> (Formula.Eventually I \<phi>) i = (case right I of \<infinity> \<Rightarrow> None | enat b \<Rightarrow> LRTP \<sigma> \<phi> (LTP_f \<sigma> i b))"
| "LRTP \<sigma> (Formula.Always I \<phi>) i = (case right I of \<infinity> \<Rightarrow> None | enat b \<Rightarrow> LRTP \<sigma> \<phi> (LTP_f \<sigma> i b))" 
| "LRTP \<sigma> (Formula.Since \<phi> I \<psi>) i = max_opt (LRTP \<sigma> \<phi> i) (LRTP \<sigma> \<psi> (LTP_p_safe \<sigma> i I))"
| "LRTP \<sigma> (Formula.Until \<phi> I \<psi>) i = (case right I of \<infinity> \<Rightarrow> None | enat b \<Rightarrow> max_opt (LRTP \<sigma> \<phi> ((LTP_f \<sigma> i b)-1)) (LRTP \<sigma> \<psi> (LTP_f \<sigma> i b)))"

lemma fb_LRTP: 
  assumes "Formula.future_bounded \<phi>"
  shows "\<not> Option.is_none (LRTP \<sigma> \<phi> i)"
  using assms
  by (induction \<sigma> \<phi> i rule: LRTP.induct) 
    (auto simp add: max_opt_def Option.is_none_def)

lemma not_none_fb_LRTP:
  assumes "Formula.future_bounded \<phi>"
  shows "(LRTP \<sigma> \<phi> i) \<noteq> None"
  using assms fb_LRTP by (auto simp add: Option.is_none_def)

lemma is_some_fb_LRTP:
  assumes "Formula.future_bounded \<phi>"
  shows "\<exists>j. (LRTP \<sigma> \<phi> i) = Some j"
  using assms fb_LRTP by (auto simp add: Option.is_none_def)

lemma i_ETP_tau: "i \<ge> ETP \<sigma> n \<longleftrightarrow> \<tau> \<sigma> i \<ge> n"
proof
  assume P: "i \<ge> ETP \<sigma> n"
  define j where j_def: "j \<equiv> ETP \<sigma> n"
  then have i_j: "\<tau> \<sigma> i \<ge> \<tau> \<sigma> j" using P by auto
  from j_def have "\<tau> \<sigma> j \<ge> n"
    unfolding ETP_def using LeastI_ex ex_le_\<tau> by force
  then show "\<tau> \<sigma> i \<ge> n" using i_j by auto
next
  assume Q: "\<tau> \<sigma> i \<ge> n"
  then show "ETP \<sigma> n \<le> i" unfolding ETP_def
    by (auto simp add: Least_le)
qed

lemma tau_LTP_k: 
  assumes "\<tau> \<sigma> 0 \<le> n" "LTP \<sigma> n < k"
  shows "\<tau> \<sigma> k > n"
proof -
  have "finite {i. \<tau> \<sigma> i \<le> n}"
    by (metis Suc_le_eq i_ETP_tau infinite_nat_iff_unbounded_le leD mem_Collect_eq)
  then show ?thesis
    using assms(2) Max.coboundedI linorder_not_less
    unfolding LTP_def by auto
qed

lemma i_LTP_tau:
  assumes n_asm: "n \<ge> \<tau> \<sigma> 0"
  shows "(i \<le> LTP \<sigma> n \<longleftrightarrow> \<tau> \<sigma> i \<le> n)"
proof
  define A and j where A_def: "A \<equiv> {i. \<tau> \<sigma> i \<le> n}" and j_def: "j \<equiv> LTP \<sigma> n"
  assume P: "i \<le> LTP \<sigma> n"
  from n_asm A_def have A_ne: "A \<noteq> {}" by auto
  from j_def have i_j: "\<tau> \<sigma> i \<le> \<tau> \<sigma> j" using P by auto
  have not_in: "k \<notin> A" if "j < k" for k
    using n_asm that tau_LTP_k leD
    unfolding A_def j_def by blast
  then have "A \<subseteq> {0..<Suc j}"
    using assms not_less_eq
    unfolding A_def j_def 
    by fastforce
  then have fin_A: "finite A"
    using subset_eq_atLeast0_lessThan_finite[of A "Suc j"]
    by simp
  from A_ne j_def have "\<tau> \<sigma> j \<le> n"
    using Max_in[of A] A_def fin_A 
    unfolding LTP_def 
    by simp
  then show "\<tau> \<sigma> i \<le> n" using i_j by auto
next
  define A and j where A_def: "A \<equiv> {i. \<tau> \<sigma> i \<le> n}" and j_def: "j \<equiv> LTP \<sigma> n"
  assume Q: "\<tau> \<sigma> i \<le> n" 
  have not_in: "k \<notin> A" if "j < k" for k
    using n_asm that tau_LTP_k leD
    unfolding A_def j_def by blast
  then have "A \<subseteq> {0..<Suc j}"
    using assms not_less_eq
    unfolding A_def j_def 
    by fastforce
  then have fin_A: "finite A"
    using subset_eq_atLeast0_lessThan_finite[of A "Suc j"]
    by simp
  moreover have "i \<in> A" using Q A_def by auto
  ultimately show "i \<le> LTP \<sigma> n" 
    using Max_ge[of A] A_def 
    unfolding LTP_def
    by auto
qed

lemma ETP_\<delta>: "i \<ge> ETP \<sigma> (\<tau> \<sigma> l + n) \<Longrightarrow> \<delta> \<sigma> i l \<ge> n"
proof -
  assume P: "i \<ge> ETP \<sigma> (\<tau> \<sigma> l + n)"
  then have "\<tau> \<sigma> i \<ge> \<tau> \<sigma> l + n" by (auto simp add: i_ETP_tau)
  then show ?thesis by auto
qed

lemma ETP_ge: "ETP \<sigma> (\<tau> \<sigma> l + n + 1) > l"
proof -
  define j where j_def: "j \<equiv> \<tau> \<sigma> l + n + 1"
  then have etp_j: "\<tau> \<sigma> (ETP \<sigma> j) \<ge> j" unfolding ETP_def
    using LeastI_ex ex_le_\<tau> by force
  then have "\<tau> \<sigma> (ETP \<sigma> j) > \<tau> \<sigma> l" using j_def by auto
  then show ?thesis using j_def less_\<tau>D by blast
qed

lemma i_le_LTPi: "i \<le> LTP \<sigma> (\<tau> \<sigma> i)"
  using \<tau>_mono i_LTP_tau[of \<sigma> "\<tau> \<sigma> i" i]
  by auto

lemma i_le_LTPi_add: "i \<le> LTP \<sigma> (\<tau> \<sigma> i + n)"
  using i_le_LTPi
  by (simp add: add_increasing2 i_LTP_tau)

lemma i_le_LTPi_minus: "\<tau> \<sigma> 0 + n \<le> \<tau> \<sigma> i \<Longrightarrow> i > 0 \<Longrightarrow> n > 0 \<Longrightarrow>
  LTP \<sigma> (\<tau> \<sigma> i - n) < i"
  unfolding LTP_def
  apply (subst Max_less_iff)
    apply (auto simp: finite_nat_set_iff_bounded_le)
  subgoal apply (rule exI[of _ i]; auto)
    apply (erule contrapos_pp) back back back
    apply (auto simp: not_le dest!: \<tau>_mono[of i _ \<sigma>] less_imp_le[of i])
    done
  subgoal apply (rule exI[of _ 0]; auto) done
  subgoal for a
    apply (erule contrapos_pp)
    apply (auto simp: not_less dest!: \<tau>_mono[of i a \<sigma>])
    done
  done

lemma i_ge_etpi: "ETP \<sigma> (\<tau> \<sigma> i) \<le> i"
  using i_ETP_tau by auto

lemma enat_trans[simp]: "enat i \<le> enat j \<and> enat j \<le> enat k \<Longrightarrow> enat i \<le> enat k"
  by auto

lemma not_sat_SinceD:
  assumes unsat: "\<not> Formula.sat \<sigma> v i (Formula.Since \<phi> I \<psi>)" and
    witness: "\<exists>j \<le> i. mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> Formula.sat \<sigma> v j \<psi>"
  shows "\<exists>j \<le> i. ETP \<sigma> (case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> \<tau> \<sigma> i - n) \<le> j \<and> \<not> Formula.sat \<sigma> v j \<phi>
  \<and> (\<forall>k \<in> {j .. (min i (LTP \<sigma> (\<tau> \<sigma> i - left I)))}. \<not> Formula.sat \<sigma> v k \<psi>)"
proof -
  define A and j where A_def: "A \<equiv> {j. j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> Formula.sat \<sigma> v j \<psi>}"
    and j_def: "j \<equiv> Max A"
  from witness have j: "j \<le> i" "Formula.sat \<sigma> v j \<psi>" "mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I"
    using Max_in[of A] unfolding j_def[symmetric] unfolding A_def
    by auto
  moreover
  from j(3) have "ETP \<sigma> (case right I of enat n \<Rightarrow> \<tau> \<sigma> i - n | \<infinity> \<Rightarrow> 0) \<le> j"
    unfolding ETP_def by (intro Least_le) (auto split: enat.splits)
  moreover
  { fix j
    assume "\<tau> \<sigma> j \<le> \<tau> \<sigma> i"
    moreover obtain k where "\<tau> \<sigma> i < \<tau> \<sigma> k" "i < k"
      by (meson ex_le_\<tau> gt_ex less_le_trans)
    ultimately have "j \<le> ETP \<sigma> (Suc (\<tau> \<sigma> i))"
      unfolding ETP_def
      apply -
      apply (rule LeastI2[of _ k])
       apply (auto simp: Suc_le_eq)
      by (meson \<tau>_mono leD less_le_trans linear)
  } note * = this
  { fix k
    assume k: "k \<in> {j <.. (min i (LTP \<sigma> (\<tau> \<sigma> i - left I)))}"
    with j(3) have "mem (\<tau> \<sigma> i - \<tau> \<sigma> k) I"
      unfolding LTP_def
      apply (auto simp: le_diff_conv2 add.commute)
       apply (subst (asm) Max_ge_iff)
         apply auto
        prefer 2
      using \<tau>_mono le_trans nat_add_left_cancel_le apply blast
       apply (rule finite_subset[of _ "{0 .. ETP \<sigma> (\<tau> \<sigma> i + 1)}"])
        apply (auto simp: * Suc_le_eq) [2]
      apply (cases "right I")
       apply (auto simp: le_diff_conv)
      by (meson \<tau>_mono add_mono_thms_linordered_semiring(2) le_trans less_imp_le)

    with Max_ge[of A k] k have "\<not> Formula.sat \<sigma> v k \<psi>"
      unfolding j_def[symmetric] unfolding A_def
      by auto
  }
  ultimately show ?thesis using unsat
    by (auto dest!: spec[of _ j])
qed

lemma min_not_in: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> x < Min A \<Longrightarrow> x \<notin> A"
  by auto

lemma not_sat_UntilD:
  assumes unsat: "\<not> (Formula.sat \<sigma> v i (Formula.Until \<phi> I \<psi>))"
    and witness: "\<exists>j \<ge> i. mem (\<delta> \<sigma> j i) I \<and> Formula.sat \<sigma> v j \<psi>"
  shows "\<exists>j \<ge> i. (case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> j < LTP \<sigma> (\<tau> \<sigma> i + n))
  \<and> \<not> (Formula.sat \<sigma> v j \<phi>) \<and> (\<forall>k \<in> {(max i (ETP \<sigma> (\<tau> \<sigma> i + left I))) .. j}.
   \<not> Formula.sat \<sigma> v k \<psi>)"
proof -
  from \<tau>_mono have i0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> i" by auto
  from witness obtain jmax where jmax: "jmax \<ge> i" "Formula.sat \<sigma> v jmax \<psi>"
    "mem (\<delta> \<sigma> jmax i) I" by blast
  define A and j where A_def: "A \<equiv> {j. j \<ge> i \<and> j \<le> jmax
  \<and> mem (\<delta> \<sigma> j i) I \<and> Formula.sat \<sigma> v j \<psi>}" and j_def: "j \<equiv> Min A"
  have j: "j \<ge> i" "Formula.sat \<sigma> v j \<psi>" "mem (\<delta> \<sigma> j i) I"
    using A_def j_def jmax Min_in[of A]
    unfolding j_def[symmetric] unfolding A_def
    by fastforce+
  moreover have "case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> j \<le> LTP \<sigma> (\<tau> \<sigma> i + n)"
    using i_LTP_tau[of \<sigma> j]
    apply (auto split: enat.splits)
    by (smt (verit, ccfv_SIG) \<tau>_mono add_diff_cancel_left' enat_ord_simps(1) i0 i_LTP_tau j(1) j(3) le_add1 le_add_diff_inverse2 le_diff_conv2 le_trans)
  moreover
  { fix k
    assume k_def: "k \<in> {(max i (ETP \<sigma> (\<tau> \<sigma> i + left I))) ..< j}"
    then have ki: "\<tau> \<sigma> k \<ge> \<tau> \<sigma> i + left I" using i_ETP_tau by auto
    with k_def have kj: "k < j" by auto
    then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> j" by auto
    then have "\<delta> \<sigma> k i \<le> \<delta> \<sigma> j i" by auto
    with this j(3) have "enat (\<delta> \<sigma> k i) \<le> right I"
      by (meson enat_ord_simps(1) order_subst2)
    with this ki j(3) have mem_k: "mem (\<delta> \<sigma> k i) I"
      unfolding ETP_def by (auto simp: Least_le)

    with j_def have "j \<le> jmax" using Min_in[of A]
      using jmax A_def
      by (metis (mono_tags, lifting) Collect_empty_eq
          finite_nat_set_iff_bounded_le mem_Collect_eq order_refl)
    with this k_def have kjm: "k \<le> jmax" by auto

    with this mem_k ki Min_le[of A k] min_not_in[of A k] k_def have "k \<notin> A"
      unfolding j_def[symmetric] unfolding A_def unfolding ETP_def
      using finite_nat_set_iff_bounded_le kj by blast
    with this mem_k k_def kjm have "\<not> Formula.sat \<sigma> v k \<psi>"
      by (simp add: A_def) }
  ultimately show ?thesis using unsat
    by (auto split: enat.splits dest!: spec[of _ j])
qed

subsection \<open>Soundness and Completeness\<close>

inductive SAT and VIO :: "'a Formula.trace \<Rightarrow> 'a Formula.env \<Rightarrow> nat \<Rightarrow> 'a Formula.formula \<Rightarrow> bool" for \<sigma> where
  STT: "SAT \<sigma> v i Formula.TT"
| VFF: "VIO \<sigma> v i Formula.FF"
| SPred: "(r, Formula.eval_trms v ts) \<in> \<Gamma> \<sigma> i \<Longrightarrow> SAT \<sigma> v i (Formula.Pred r ts)"
| VPred: "(r, Formula.eval_trms v ts) \<notin> \<Gamma> \<sigma> i \<Longrightarrow> VIO \<sigma> v i (Formula.Pred r ts)"
| SEq_Const: "v x = c \<Longrightarrow> SAT \<sigma> v i (Formula.Eq_Const x c)"
| VEq_Const: "v x \<noteq> c \<Longrightarrow> VIO \<sigma> v i (Formula.Eq_Const x c)"
| SNeg: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (Formula.Neg \<phi>)"
| VNeg: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i (Formula.Neg \<phi>)"
| SOrL: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (Formula.Or \<phi> \<psi>)"
| SOrR: "SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (Formula.Or \<phi> \<psi>)"
| VOr: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (Formula.Or \<phi> \<psi>)"
| SAnd: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (Formula.And \<phi> \<psi>)"
| VAndL: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i (Formula.And \<phi> \<psi>)"
| VAndR: "VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (Formula.And \<phi> \<psi>)"
| SImpL: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (Formula.Imp \<phi> \<psi>)"
| SImpR: "SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (Formula.Imp \<phi> \<psi>)"
| VImp: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (Formula.Imp \<phi> \<psi>)"
| SIffSS: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (Formula.Iff \<phi> \<psi>)"
| SIffVV: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (Formula.Iff \<phi> \<psi>)"
| VIffSV: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (Formula.Iff \<phi> \<psi>)"
| VIffVS: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (Formula.Iff \<phi> \<psi>)"
| SExists: "\<exists>z. SAT \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> SAT \<sigma> v i (Formula.Exists x \<phi>)"
| VExists: "\<forall>z. VIO \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> VIO \<sigma> v i (Formula.Exists x \<phi>)"
| SForall: "\<forall>z. SAT \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> SAT \<sigma> v i (Formula.Forall x \<phi>)"
| VForall: "\<exists>z. VIO \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> VIO \<sigma> v i (Formula.Forall x \<phi>)"
| SPrev: "i > 0 \<Longrightarrow> mem (\<Delta> \<sigma> i) I \<Longrightarrow> SAT \<sigma> v (i-1) \<phi> \<Longrightarrow> SAT \<sigma> v i (Formula.Prev I \<phi>)"
| VPrev: "i > 0 \<Longrightarrow> VIO \<sigma> v (i-1) \<phi> \<Longrightarrow> VIO \<sigma> v i (Formula.Prev I \<phi>)"
| VPrevZ: "i = 0 \<Longrightarrow> VIO \<sigma> v i (Formula.Prev I \<phi>)"
| VPrevOutL: "i > 0 \<Longrightarrow> (\<Delta> \<sigma> i) < (left I) \<Longrightarrow> VIO \<sigma> v i (Formula.Prev I \<phi>)"
| VPrevOutR: "i > 0 \<Longrightarrow> enat (\<Delta> \<sigma> i) > (right I) \<Longrightarrow> VIO \<sigma> v i (Formula.Prev I \<phi>)"
| SNext: "mem (\<Delta> \<sigma> (i+1)) I \<Longrightarrow> SAT \<sigma> v (i+1) \<phi> \<Longrightarrow> SAT \<sigma> v i (Formula.Next I \<phi>)"
| VNext: "VIO \<sigma> v (i+1) \<phi> \<Longrightarrow> VIO \<sigma> v i (Formula.Next I \<phi>)"
| VNextOutL: "(\<Delta> \<sigma> (i+1)) < (left I) \<Longrightarrow> VIO \<sigma> v i (Formula.Next I \<phi>)"
| VNextOutR: "enat (\<Delta> \<sigma> (i+1)) > (right I) \<Longrightarrow> VIO \<sigma> v i (Formula.Next I \<phi>)"
| SOnce: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I \<Longrightarrow> SAT \<sigma> v j \<phi> \<Longrightarrow> SAT \<sigma> v i (Formula.Once I \<phi>)"
| VOnceOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> VIO \<sigma> v i (Formula.Once I \<phi>)"
| VOnce: "j = (case right I of \<infinity> \<Rightarrow> 0 
               | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
          (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow>
          (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> VIO \<sigma> v k \<phi>) \<Longrightarrow> VIO \<sigma> v i (Formula.Once I \<phi>)"
| SEventually: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> SAT \<sigma> v j \<phi> \<Longrightarrow> SAT \<sigma> v i (Formula.Eventually I \<phi>)"
| VEventually: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..}
                           | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> VIO \<sigma> v k \<phi>) \<Longrightarrow> 
                VIO \<sigma> v i (Formula.Eventually I \<phi>)"
| SHistorically: "j = (case right I of \<infinity> \<Rightarrow> 0
                       | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
                 (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow>
                 (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow> SAT \<sigma> v i (Formula.Historically I \<phi>)"
| SHistoricallyOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> SAT \<sigma> v i (Formula.Historically I \<phi>)"
| VHistorically: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I  \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> VIO \<sigma> v i (Formula.Historically I \<phi>)"
| SAlways: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..} 
                       | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow>
            SAT \<sigma> v i (Formula.Always I \<phi>)"
| VAlways: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> VIO \<sigma> v i (Formula.Always I \<phi>)"
| SSince: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I  \<Longrightarrow> SAT \<sigma> v j \<psi> \<Longrightarrow> (\<And>k. k \<in> {j <.. i} \<Longrightarrow> 
           SAT \<sigma> v k \<phi>) \<Longrightarrow> SAT \<sigma> v i (Formula.Since \<phi> I \<psi>)"
| VSinceOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> VIO \<sigma> v i (Formula.Since \<phi> I \<psi>)"
| VSince: "(case right I of \<infinity> \<Rightarrow> True 
            | enat b \<Rightarrow> ETP \<sigma> ((\<tau> \<sigma> i) - b) \<le> j) \<Longrightarrow> 
           j \<le> i \<Longrightarrow> (\<tau> \<sigma> 0) + left I \<le> (\<tau> \<sigma> i) \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow>
           (\<And>k. k \<in> {j .. (LTP_p \<sigma> i I)} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> VIO \<sigma> v i (Formula.Since \<phi> I \<psi>)"
| VSinceInf: "j = (case right I of \<infinity> \<Rightarrow> 0 
                   | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
             (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow> 
             (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> VIO \<sigma> v i (Formula.Since \<phi> I \<psi>)"
| SUntil: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> SAT \<sigma> v j \<psi> \<Longrightarrow> (\<And>k. k \<in> {i ..< j} \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow> 
           SAT \<sigma> v i (Formula.Until \<phi> I \<psi>)"
| VUntil: "(case right I of \<infinity> \<Rightarrow> True 
            | enat b \<Rightarrow> j < LTP_f \<sigma> i b) \<Longrightarrow> 
           j \<ge> i \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> (\<And>k. k \<in> {ETP_f \<sigma> i I .. j} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> 
           VIO \<sigma> v i (Formula.Until \<phi> I \<psi>)"
| VUntilInf: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..} 
                         | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow>
              VIO \<sigma> v i (Formula.Until \<phi> I \<psi>)"

lemma soundness_raw: "(SAT \<sigma> v i \<phi> \<longrightarrow> Formula.sat \<sigma> v i \<phi>) \<and> (VIO \<sigma> v i \<phi> \<longrightarrow> \<not> Formula.sat \<sigma> v i \<phi>)"
proof (induct v i \<phi> rule: SAT_VIO.induct)
  case (VOnceOut i I v \<phi>)
  { fix j
    from \<tau>_mono have j0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> j" by auto
    then have "\<tau> \<sigma> i < \<tau> \<sigma> j + left I" using VOnceOut apply simp
      using j0 by linarith
    then have "\<delta> \<sigma> i j < left I"
      using VOnceOut less_\<tau>D verit_comp_simplify1(3) by fastforce
    then have "\<not> mem (\<delta> \<sigma> i j) I" by auto }
  then show ?case
    by auto
next
  case (VOnce j I i v \<phi>)
  { fix k
    assume k_def: "Formula.sat \<sigma> v k \<phi> \<and> mem (\<delta> \<sigma> i k) I \<and> k \<le> i"
    then have k_tau: "\<tau> \<sigma> k \<le> \<tau> \<sigma> i - left I"
      using diff_le_mono2 by fastforce
    then have k_ltp: "k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      using VOnce i_LTP_tau add_le_imp_le_diff
      by blast
    then have "k \<notin> {j .. LTP_p \<sigma> i I}"
      using k_def VOnce k_tau
      by auto
    then have "k < j" using k_def k_ltp by auto }
  then show ?case
    using VOnce
    by (cases "right I = \<infinity>")
      (auto 0 0 simp: i_ETP_tau i_LTP_tau le_diff_conv2)
next
  case (VEventually I i v \<phi>)
  { fix k n
    assume r: "right I = enat n"
    from this have tin0: "\<tau> \<sigma> i + n \<ge> \<tau> \<sigma> 0"
      by (auto simp add: trans_le_add1)
    define j where "j = LTP \<sigma> ((\<tau> \<sigma> i) + n)"
    then have j_i: "i \<le> j"
      by (auto simp add: i_LTP_tau trans_le_add1 j_def)
    assume k_def: "Formula.sat \<sigma> v k \<phi> \<and> mem (\<delta> \<sigma> k i) I \<and> i \<le> k"
    then have "\<tau> \<sigma> k \<ge> \<tau> \<sigma> i + left I"
      using le_diff_conv2 by auto
    then have k_etp: "k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      using i_ETP_tau by blast
    from this k_def VEventually have "k \<notin> {ETP_f \<sigma> i I .. j}"
      by (auto simp: r j_def)
    then have "j < k" using r k_def k_etp by auto
    from k_def r have "\<delta> \<sigma> k i \<le> n" by auto
    then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + n" by auto
    then have "k \<le> j" using tin0 i_LTP_tau by (auto simp add: j_def) }
  note aux = this
  show ?case
  proof (cases "right I")
    case (enat n)
    show ?thesis
      using VEventually aux
      apply (simp add: i_ETP_tau le_diff_conv2 enat add_le_imp_le_diff)
      by (metis \<tau>_mono le_add_diff_inverse nat_add_left_cancel_le)
  next
    case infinity
    show ?thesis
      using VEventually
      by (auto simp: infinity i_ETP_tau le_diff_conv2)
  qed
next
  case (SHistorically j I i v \<phi>)
  { fix k
    assume k_def: "\<not> Formula.sat \<sigma> v k \<phi> \<and> mem (\<delta> \<sigma> i k) I \<and> k \<le> i"
    then have k_tau: "\<tau> \<sigma> k \<le> \<tau> \<sigma> i - left I"
      using diff_le_mono2 by fastforce
    then have k_ltp: "k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      using SHistorically i_LTP_tau add_le_imp_le_diff
      by blast
    then have "k \<notin> {j .. LTP_p \<sigma> i I}"
      using k_def SHistorically k_tau
      by auto
    then have "k < j" using k_def k_ltp by auto }
  then show ?case
    using SHistorically
    by (cases "right I = \<infinity>")
      (auto 0 0 simp add: le_diff_conv2 i_ETP_tau i_LTP_tau)
next
  case (SHistoricallyOut i I v \<phi>)
  { fix j
    from \<tau>_mono have j0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> j" by auto
    then have "\<tau> \<sigma> i < \<tau> \<sigma> j + left I" using SHistoricallyOut apply simp
      using j0 by linarith
    then have "\<delta> \<sigma> i j < left I"
      using SHistoricallyOut less_\<tau>D not_le by fastforce
    then have "\<not> mem (\<delta> \<sigma> i j) I" by auto }
  then show ?case by auto
next
  case (SAlways I i v \<phi>)
  { fix k n
    assume r: "right I = enat n"
    from this SAlways have tin0: "\<tau> \<sigma> i + n \<ge> \<tau> \<sigma> 0"
      by (auto simp add: trans_le_add1)
    define j where "j = LTP \<sigma> ((\<tau> \<sigma> i) + n)"
    from SAlways have j_i: "i \<le> j"
      by (auto simp add: i_LTP_tau trans_le_add1 j_def)
    assume k_def: "\<not> Formula.sat \<sigma> v k \<phi> \<and> mem (\<delta> \<sigma> k i) I \<and> i \<le> k"
    then have "\<tau> \<sigma> k \<ge> \<tau> \<sigma> i + left I"
      using le_diff_conv2 by auto
    then have k_etp: "k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      using SAlways i_ETP_tau by blast
    from this k_def SAlways have "k \<notin> {ETP_f \<sigma> i I .. j}"
      by (auto simp: r j_def)
    then have "j < k" using SAlways k_def k_etp by simp
    from k_def r have "\<delta> \<sigma> k i \<le> n" by simp
    then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + n" by simp
    then have "k \<le> j"
      using tin0 i_LTP_tau  
      by (auto simp add: j_def) }
  note aux = this
  show ?case
  proof (cases "right I")
    case (enat n)
    show ?thesis
      using SAlways aux
      apply (simp add: i_ETP_tau le_diff_conv2 enat)
      by (metis Groups.ab_semigroup_add_class.add.commute add_le_imp_le_diff)
  next
    case infinity
    show ?thesis
      using SAlways
      by (auto simp: infinity i_ETP_tau le_diff_conv2)
  qed
next
  case (VSinceOut i I v \<phi> \<psi>)
  { fix j
    from \<tau>_mono have j0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> j" by auto
    then have "\<tau> \<sigma> i < \<tau> \<sigma> j + left I" using VSinceOut by linarith
    then have "\<delta> \<sigma> i j < left I" using VSinceOut j0
      by (metis add.commute gr_zeroI leI less_\<tau>D less_diff_conv2 order_less_imp_not_less zero_less_diff)
    then have "\<not> mem (\<delta> \<sigma> i j) I" by auto }
  then show ?case using VSinceOut by auto
next
  case (VSince I i j v \<phi> \<psi>)
  { fix k
    assume k_def: "Formula.sat \<sigma> v k \<psi> \<and> mem (\<delta> \<sigma> i k) I \<and> k \<le> i"
    then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> i - left I" using diff_le_mono2 by fastforce
    then have k_ltp: "k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      using VSince i_LTP_tau add_le_imp_le_diff
      by blast
    then have "k < j" using k_def VSince apply simp
      by (meson diff_is_0_eq not_gr_zero zero_less_diff)
    then have "j \<in> {k <.. i} \<and> \<not> Formula.sat \<sigma> v j \<phi>" using VSince
      by auto }
  then show ?case using VSince
    by force
next
  case (VSinceInf j I i v \<psi> \<phi>)
  { fix k
    assume k_def: "Formula.sat \<sigma> v k \<psi> \<and> mem (\<delta> \<sigma> i k) I \<and> k \<le> i"
    then have k_tau: "\<tau> \<sigma> k \<le> \<tau> \<sigma> i - left I"
      using diff_le_mono2 by fastforce
    then have k_ltp: "k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      using VSinceInf i_LTP_tau add_le_imp_le_diff
      by blast
    then have "k \<notin> {j .. LTP_p \<sigma> i I}"
      using k_def VSinceInf k_tau
      by auto
    then have "k < j" using k_def k_ltp by auto }
  then show ?case
    using VSinceInf
    by (cases "right I = \<infinity>")
      (auto 0 0 simp: i_ETP_tau i_LTP_tau le_diff_conv2)
next
  case (VUntil I j i v \<phi> \<psi>)
  { fix k
    assume k_def: "Formula.sat \<sigma> v k \<psi> \<and> mem (\<delta> \<sigma> k i) I \<and> i \<le> k"
    then have "\<tau> \<sigma> k \<ge> \<tau> \<sigma> i + left I"
      using le_diff_conv2 by auto
    then have k_etp: "k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      using VUntil i_ETP_tau by blast
    from this k_def VUntil have "k \<notin> {ETP_f \<sigma> i I .. j}" by auto
    then have "j < k" using k_etp k_def by auto
    then have "j \<in> {i ..< k} \<and> VIO \<sigma> v j \<phi>" using VUntil k_def
      by auto }
  then show ?case
    using VUntil by force
next
  case (VUntilInf I i v \<psi> \<phi>)
  { fix k n
    assume r: "right I = enat n"
    from this VUntilInf have tin0: "\<tau> \<sigma> i + n \<ge> \<tau> \<sigma> 0"
      by (auto simp add: trans_le_add1)
    define j where "j = LTP \<sigma> ((\<tau> \<sigma> i) + n)"
    from VUntilInf have j_i: "i \<le> j"
      by (auto simp add: i_LTP_tau trans_le_add1 j_def)
    assume k_def: "Formula.sat \<sigma> v k \<psi> \<and> mem (\<delta> \<sigma> k i) I \<and> i \<le> k"
    then have "\<tau> \<sigma> k \<ge> \<tau> \<sigma> i + left I"
      using le_diff_conv2 by auto
    then have k_etp: "k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      using VUntilInf i_ETP_tau by blast
    from this k_def VUntilInf have "k \<notin> {ETP_f \<sigma> i I .. j}"
      by (auto simp: r j_def)
    then have "j < k" using VUntilInf k_def k_etp by auto
    from k_def r have "\<delta> \<sigma> k i \<le> n" by auto
    then have "\<tau> \<sigma> k \<le> \<tau> \<sigma> i + n" by auto
    then have "k \<le> j"
      using tin0 VUntilInf i_LTP_tau r k_def 
      by (force simp add: j_def) }
  note aux = this
  show ?case
  proof (cases "right I")
    case (enat n)
    show ?thesis
      using VUntilInf aux
      apply (simp add: i_ETP_tau le_diff_conv2 enat add_le_imp_le_diff)
      by (metis \<tau>_mono le_add_diff_inverse nat_add_left_cancel_le)
  next
    case infinity
    show ?thesis
      using VUntilInf
      by (auto simp: infinity i_ETP_tau le_diff_conv2)
  qed
qed (auto simp: fun_upd_def split: nat.splits)

lemmas soundness = soundness_raw[THEN conjunct1, THEN mp] soundness_raw[THEN conjunct2, THEN mp]

lemma completeness_raw: "(Formula.sat \<sigma> v i \<phi> \<longrightarrow> SAT \<sigma> v i \<phi>) \<and> (\<not> Formula.sat \<sigma> v i \<phi> \<longrightarrow> VIO \<sigma> v i \<phi>)"
proof (induct \<phi> arbitrary: v i)
  case (Prev I \<phi>)
  show ?case using Prev
    by (auto intro: SAT_VIO.SPrev SAT_VIO.VPrev SAT_VIO.VPrevOutL SAT_VIO.VPrevOutR SAT_VIO.VPrevZ split: nat.splits)
next
  case (Once I \<phi>)
  { assume "Formula.sat \<sigma> v i (Formula.Once I \<phi>)"
    with Once have "SAT \<sigma> v i (Formula.Once I \<phi>)"
      by (auto intro: SAT_VIO.SOnce) }
  moreover
  { assume i_l: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I"
    with Once have "VIO \<sigma> v i (Formula.Once I \<phi>)"
      by (auto intro: SAT_VIO.VOnceOut) }
  moreover
  { assume unsat: "\<not> Formula.sat \<sigma> v i (Formula.Once I \<phi>)"
      and i_ge: "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
    with Once have "VIO \<sigma> v i (Formula.Once I \<phi>)"
      by (auto intro!: SAT_VIO.VOnce simp: i_LTP_tau i_ETP_tau
          split: enat.splits) }
  ultimately show ?case
    by force
next
  case (Historically I \<phi>)
  from \<tau>_mono have i0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> i" by auto
  { assume sat: "Formula.sat \<sigma> v i (Formula.Historically I \<phi>)"
      and i_ge: "\<tau> \<sigma> i \<ge> \<tau> \<sigma> 0 + left I"
    with Historically have "SAT \<sigma> v i (Formula.Historically I \<phi>)"
      using le_diff_conv
      by (auto intro!: SAT_VIO.SHistorically simp: i_LTP_tau i_ETP_tau
          split: enat.splits) }
  moreover
  { assume "\<not> Formula.sat \<sigma> v i (Formula.Historically I \<phi>)"
    with Historically have "VIO \<sigma> v i (Formula.Historically I \<phi>)"
      by (auto intro: SAT_VIO.VHistorically) }
  moreover
  { assume i_l: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I"
    with Historically have "SAT \<sigma> v i (Formula.Historically I \<phi>)"
      by (auto intro: SAT_VIO.SHistoricallyOut) }
  ultimately show ?case
    by force
next
  case (Eventually I \<phi>)
  from \<tau>_mono have i0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> i" by auto
  { assume "Formula.sat \<sigma> v i (Formula.Eventually I \<phi>)"
    with Eventually have "SAT \<sigma> v i (Formula.Eventually I \<phi>)"
      by (auto intro: SAT_VIO.SEventually) }
  moreover
  { assume unsat: "\<not> Formula.sat \<sigma> v i (Formula.Eventually I \<phi>)"
    with Eventually have "VIO \<sigma> v i (Formula.Eventually I \<phi>)"
      by (auto intro!: SAT_VIO.VEventually simp: add_increasing2 i0 i_LTP_tau i_ETP_tau
          split: enat.splits) }
  ultimately show ?case by auto
next
  case (Always I \<phi>)
    from \<tau>_mono have i0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> i" by auto
  { assume "\<not> Formula.sat \<sigma> v i (Formula.Always I \<phi>)"
    with Always have "VIO \<sigma> v i (Formula.Always I \<phi>)"
      by (auto intro: SAT_VIO.VAlways) }
  moreover
  { assume sat: "Formula.sat \<sigma> v i (Formula.Always I \<phi>)"
    with Always have "SAT \<sigma> v i (Formula.Always I \<phi>)"
      by (auto intro!: SAT_VIO.SAlways simp: add_increasing2 i0 i_LTP_tau i_ETP_tau le_diff_conv split: enat.splits)}
  ultimately show ?case by auto
next
  case (Since \<phi> I \<psi>)
  { assume "Formula.sat \<sigma> v i (Formula.Since \<phi> I \<psi>)"
    with Since have "SAT \<sigma> v i (Formula.Since \<phi> I \<psi>)"
      by (auto intro: SAT_VIO.SSince) }
  moreover
  { assume i_l: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I"
    with Since have "VIO \<sigma> v i (Formula.Since \<phi> I \<psi>)"
      by (auto intro: SAT_VIO.VSinceOut) }
  moreover
  { assume unsat: "\<not> Formula.sat \<sigma> v i (Formula.Since \<phi> I \<psi>)"
      and nw: "\<forall>j\<le>i. \<not> mem (\<delta> \<sigma> i j) I \<or> \<not> Formula.sat \<sigma> v j \<psi>"
      and i_ge: "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
    with Since have "VIO \<sigma> v i (Formula.Since \<phi> I \<psi>)"
      by (auto intro!: SAT_VIO.VSinceInf simp: i_LTP_tau i_ETP_tau
          split: enat.splits)}
  moreover
  { assume unsat: "\<not> Formula.sat \<sigma> v i (Formula.Since \<phi> I \<psi>)"
      and jw: "\<exists>j\<le>i. mem (\<delta> \<sigma> i j) I \<and> Formula.sat \<sigma> v j \<psi>"
      and i_ge: "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
    from unsat jw not_sat_SinceD[of \<sigma> v i \<phi> I \<psi>]
    obtain j where j: "j \<le> i"
      "case right I of \<infinity> \<Rightarrow> True | enat n \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - n) \<le> j"
      "\<not> Formula.sat \<sigma> v j \<phi>" "(\<forall>k \<in> {j .. (min i (LTP \<sigma> (\<tau> \<sigma> i - left I)))}.
      \<not> Formula.sat \<sigma> v k \<psi>)" by (auto split: enat.splits)
    with Since have "VIO \<sigma> v i (Formula.Since \<phi> I \<psi>)"
      using i_ge unsat jw
      by (auto intro!: SAT_VIO.VSince) }
  ultimately show ?case
    by (force simp del: sat.simps)
next
  case (Until \<phi> I \<psi>)
  from \<tau>_mono have i0: "\<tau> \<sigma> 0 \<le> \<tau> \<sigma> i" by auto
  { assume "Formula.sat \<sigma> v i (Formula.Until \<phi> I \<psi>)"
    with Until have "SAT \<sigma> v i (Formula.Until \<phi> I \<psi>)"
      by (auto intro: SAT_VIO.SUntil) }
  moreover
  { assume unsat: "\<not> Formula.sat \<sigma> v i (Formula.Until \<phi> I \<psi>)"
      and witness: "\<exists>j \<ge> i. mem (\<delta> \<sigma> j i) I \<and> Formula.sat \<sigma> v j \<psi>"
    from this Until not_sat_UntilD[of \<sigma> v i \<phi> I \<psi>] obtain j
      where j: "j \<ge> i" "(case right I of \<infinity> \<Rightarrow> True | enat n
      \<Rightarrow> j < LTP \<sigma> (\<tau> \<sigma> i + n))" "\<not> (Formula.sat \<sigma> v j \<phi>)"
        "(\<forall>k \<in> {(max i (ETP \<sigma> (\<tau> \<sigma> i + left I))) .. j}. \<not> Formula.sat \<sigma> v k \<psi>)"
      by auto
    with Until have "VIO \<sigma> v i (Formula.Until \<phi> I \<psi>)"
      using unsat witness 
      by (auto intro!: SAT_VIO.VUntil) }
  moreover
  { assume unsat: "\<not> Formula.sat \<sigma> v i (Formula.Until \<phi> I \<psi>)"
      and no_witness: "\<forall>j \<ge> i. \<not> mem (\<delta> \<sigma> j i) I \<or> \<not> Formula.sat \<sigma> v j \<psi>"
    with Until have "VIO \<sigma> v i (Formula.Until \<phi> I \<psi>)"
      by (auto intro!: SAT_VIO.VUntilInf simp: add_increasing2 i0 i_LTP_tau i_ETP_tau
          split: enat.splits)
  }
  ultimately show ?case by auto
qed (auto intro: SAT_VIO.intros)

lemmas completeness = completeness_raw[THEN conjunct1, THEN mp] completeness_raw[THEN conjunct2, THEN mp]


lemma SAT_or_VIO: "SAT \<sigma> v i \<phi> \<or> VIO \<sigma> v i \<phi>"
  using completeness[of \<sigma> v i \<phi>] by auto

end

subsection \<open>Proof Objects\<close>

lemma part_list_set_eq: 
  "{xs :: ('d set \<times> 'a) list. (\<Union>X \<in> fst ` set xs. X) = UNIV
    \<and> (\<forall>i < length xs. \<forall>j < length xs. i \<noteq> j 
      \<longrightarrow> fst (xs ! i) \<inter> fst (xs ! j) = {}) \<and> {} \<notin> fst ` set xs}
  = {xs :: ('d set \<times> 'a) list. partition_on UNIV (set (map fst xs)) \<and> distinct (map fst xs)}"
proof ((intro set_eqI iffI; clarsimp simp: partition_on_def), goal_cases)
  case (1 xs)
  hence "disjoint (fst ` set xs)"
    by (metis disjnt_def in_set_conv_nth pairwise_imageI)
  moreover have "distinct (map fst xs)"
    using 1
    by (smt (verit) distinct_conv_nth image_iff inf.idem 
        length_map nth_map nth_mem) 
  ultimately show ?case 
    by blast
next
  case (2 xs i j)
  hence "fst (xs ! i) \<in> fst ` set xs"
    and "fst (xs ! j) \<in> fst ` set xs"
    by auto
  moreover have "fst (xs ! i) \<noteq> fst (xs ! j)"
    using 2(4-) nth_eq_iff_index_eq 
    by fastforce 
  ultimately show ?case
    using 2(2) unfolding disjoint_def
    by blast
qed

(* 'd: domain (such that the union of 'd sets form a partition) *)
typedef ('d, 'a) part = "{xs :: ('d set \<times> 'a) list. partition_on UNIV (set (map fst xs)) \<and> distinct (map fst xs)}"
  by (rule exI[of _ "[(UNIV, undefined)]"]) 
    (auto simp: partition_on_def)

setup_lifting type_definition_part

lift_bnf (no_warn_wits, no_warn_transfer) (dead 'd, Vals: 'a) part
  unfolding part_list_set_eq[symmetric]
  by (auto simp: image_iff)

subsection \<open>\<^const>\<open>size\<close> setup\<close>

lift_definition subs :: "('d, 'a) part \<Rightarrow> 'd set list" is "map fst" .

lift_definition Subs :: "('d, 'a) part \<Rightarrow> 'd set set" is "set o map fst" .

lift_definition vals :: "('d, 'a) part \<Rightarrow> 'a list" is "map snd" .

lift_definition SubsVals :: "('d, 'a) part \<Rightarrow> ('d set \<times> 'a) set" is "set" .

lift_definition subsvals :: "('d, 'a) part \<Rightarrow> ('d set \<times> 'a) list" is "id" .

lift_definition size_part :: "('d \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> ('d, 'a) part \<Rightarrow> nat" is "\<lambda>f g. size_list (\<lambda>(x, y). sum f x + g y)" .

instantiation part :: (type, type) size begin

definition size_part where
size_part_overloaded_def: "size_part = Proof_System.size_part (\<lambda>_. 0) (\<lambda>_. 0)"

instance ..

end

lemma size_part_overloaded_simps[simp]: "size x = size (vals x)"
  unfolding size_part_overloaded_def
  by transfer (auto simp: size_list_conv_sum_list)

lemma part_size_o_map: "inj h \<Longrightarrow> size_part f g \<circ> map_part h = size_part f (g \<circ> h)"
  by (rule ext, transfer)
    (auto simp: fun_eq_iff map_prod_def o_def split_beta case_prod_beta[abs_def])

setup \<open>
BNF_LFP_Size.register_size_global \<^type_name>\<open>part\<close> \<^const_name>\<open>size_part\<close>
  @{thm size_part_overloaded_def} @{thms size_part_def size_part_overloaded_simps}
  @{thms part_size_o_map}
\<close>

lemma is_measure_size_part[measure_function]: "is_measure f \<Longrightarrow> is_measure g \<Longrightarrow> is_measure (size_part f g)"
  by (rule is_measure_trivial)

lemma size_part_estimation[termination_simp]: "x \<in> Vals xs \<Longrightarrow> y < g x \<Longrightarrow> y < size_part f g xs"
  by transfer (auto simp: termination_simp)

lemma size_part_estimation'[termination_simp]: "x \<in> Vals xs \<Longrightarrow> y \<le> g x \<Longrightarrow> y \<le> size_part f g xs"
  by transfer (auto simp: termination_simp)

lemma size_part_pointwise[termination_simp]: "(\<And>x. x \<in> Vals xs \<Longrightarrow> f x \<le> g x) \<Longrightarrow> size_part h f xs \<le> size_part h g xs"
  by transfer (force simp: image_iff intro!: size_list_pointwise)

lemma Vals_code[code]: "Vals x = set (map snd (Rep_part x))"
  by (force simp: Vals_def)

lemma Vals_transfer[transfer_rule]: "rel_fun (pcr_part (=) (=)) (=) (set \<circ> map snd) Vals"
  by (force simp: Vals_def rel_fun_def pcr_part_def cr_part_def rel_set_eq prod.rel_eq list.rel_eq)

lemma set_vals[simp]: "set (vals xs) = Vals xs"
  by transfer simp

subsection \<open>Proof Objects\<close>

datatype (dead 'd) sproof = STT nat 
  | SPred nat Formula.name "'d Formula.trm list"
  | SEq_Const nat Formula.name 'd
  | SNeg "'d vproof" 
  | SOrL "'d sproof" 
  | SOrR "'d sproof" 
  | SAnd "'d sproof" "'d sproof"
  | SImpL "'d vproof" 
  | SImpR "'d sproof"
  | SIffSS "'d sproof" "'d sproof" 
  | SIffVV "'d vproof" "'d vproof" 
  | SExists Formula.name 'd "'d sproof"
  | SForall Formula.name "('d, 'd sproof) part" 
  | SPrev "'d sproof"
  | SNext "'d sproof"
  | SOnce nat "'d sproof"
  | SEventually nat "'d sproof" 
  | SHistorically nat nat "'d sproof list" 
  | SHistoricallyOut nat
  | SAlways nat nat "'d sproof list"
  | SSince "'d sproof" "'d sproof list" 
  | SUntil "'d sproof list" "'d sproof" 
  and 'd vproof = VFF nat 
  | VPred nat Formula.name "'d Formula.trm list"
  | VEq_Const nat Formula.name 'd
  | VNeg "'d sproof" 
  | VOr "'d vproof" "'d vproof"
  | VAndL "'d vproof" 
  | VAndR "'d vproof" 
  | VImp "'d sproof" "'d vproof" 
  | VIffSV "'d sproof" "'d vproof" 
  | VIffVS "'d vproof" "'d sproof" 
  | VExists Formula.name "('d, 'd vproof) part" 
  | VForall Formula.name 'd "'d vproof"
  | VPrev "'d vproof"
  | VPrevZ
  | VPrevOutL nat 
  | VPrevOutR nat
  | VNext "'d vproof" 
  | VNextOutL nat 
  | VNextOutR nat 
  | VOnceOut nat 
  | VOnce nat nat "'d vproof list" 
  | VEventually nat nat "'d vproof list"
  | VHistorically nat "'d vproof" 
  | VAlways nat "'d vproof"
  | VSinceOut nat
  | VSince nat "'d vproof" "'d vproof list" 
  | VSinceInf nat nat "'d vproof list" 
  | VUntil nat "'d vproof list" "'d vproof"
  | VUntilInf nat nat "'d vproof list"
                                                                 
subsection \<open>Partitioned Decision Trees\<close>

(* 'd: domain; 'pt: proof tree *)
datatype ('d, 'pt) pdt = Leaf (unleaf: 'pt) | Node Formula.name "('d, ('d, 'pt) pdt) part"

type_synonym 'd "proof" = "'d sproof + 'd vproof"

type_synonym 'd expl = "('d, 'd proof) pdt"

fun vars_expl :: "'d expl \<Rightarrow> Formula.name set" where
  "vars_expl (Node x part) = {x} \<union> (\<Union>pdt \<in> Vals part. vars_expl pdt)"
| "vars_expl (Leaf pt) = {}"

lift_definition part_hd :: "('d, 'a) part \<Rightarrow> 'a" is "snd \<circ> hd" .

lift_definition tabulate :: "'d list \<Rightarrow> ('d \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> ('d, 'v) part" is
  "\<lambda>ds f z. if distinct ds then if set ds = UNIV then map (\<lambda>d. ({d}, f d)) ds else (- set ds, z) # map (\<lambda>d. ({d}, f d)) ds else [(UNIV, z)]"
  by (auto simp: o_def distinct_map inj_on_def partition_on_def disjoint_def)

lift_definition lookup_part :: "('d, 'a) part \<Rightarrow> 'd \<Rightarrow> 'a" is "\<lambda>xs d. snd (the (find (\<lambda>(D, _). d \<in> D) xs))" .

lemma part_hd_Vals[simp]: "part_hd part \<in> Vals part"
  apply transfer
  subgoal for xs
    by (cases xs) (auto simp: partition_on_def)
  done

lemma lookup_part_Vals[simp]: "lookup_part part d \<in> Vals part"
  apply transfer
  subgoal for xs d
    apply (cases "find (\<lambda>(D, _). d \<in> D) xs")
     apply (auto simp: partition_on_def find_None_iff find_Some_iff image_iff)
     apply (metis UNIV_I UN_iff prod.collapse)
    apply (metis (no_types, lifting) find_Some_iff nth_mem option.sel prod.simps(2))
    done
  done

lemma lookup_part_SubsVals: "\<exists>D. d \<in> D \<and> (D, lookup_part part d) \<in> SubsVals part"
  apply transfer
  subgoal for d xs
    apply (cases "find (\<lambda>(D, _). d \<in> D) xs")
     apply (auto simp: partition_on_def find_None_iff find_Some_iff image_iff)
     apply (metis UNIV_I UN_iff prod.collapse)
    apply (metis (mono_tags, lifting) find_Some_iff nth_mem option.sel prod.exhaust_sel prod.simps(2))
    done
  done

lemma size_lookup_part_estimation[termination_simp]: "size (lookup_part part d) < Suc (size_part (\<lambda>_. 0) size part)"
  unfolding less_Suc_eq_le
  by (rule size_part_estimation'[OF _ order_refl]) simp

lemma subsvals_part_estimation[termination_simp]: "(D, e) \<in> set (subsvals part) \<Longrightarrow> size e < Suc (size_part (\<lambda>_. 0) size part)"
  unfolding less_Suc_eq_le
  by (rule size_part_estimation'[OF _ order_refl], transfer)
    (force simp: image_iff)

lemma size_part_hd_estimation[termination_simp]: "size (part_hd part) < Suc (size_part (\<lambda>_. 0) size part)"
  unfolding less_Suc_eq_le
  by (rule size_part_estimation'[OF _ order_refl]) simp

lemma size_last_estimation[termination_simp]: "xs \<noteq> [] \<Longrightarrow> size (last xs) < size_list size xs"
  by (induct xs) auto

fun s_at :: "'d sproof \<Rightarrow> nat" and 
  v_at :: "'d vproof \<Rightarrow> nat" where
  "s_at (STT i) = i"
| "s_at (SPred i _ _) = i"
| "s_at (SEq_Const i _ _) = i"
| "s_at (SNeg vp) = v_at vp"
| "s_at (SOrL sp1) = s_at sp1"
| "s_at (SOrR sp2) = s_at sp2"
| "s_at (SAnd sp1 _) = s_at sp1"
| "s_at (SImpL vp1) = v_at vp1"
| "s_at (SImpR sp2) = s_at sp2"
| "s_at (SIffSS sp1 _) = s_at sp1"
| "s_at (SIffVV vp1 _) = v_at vp1"
| "s_at (SExists _ _ sp) = s_at sp"
| "s_at (SForall _ part) = s_at (part_hd part)"
| "s_at (SPrev sp) = s_at sp + 1"
| "s_at (SNext sp) = s_at sp - 1"
| "s_at (SOnce i _) = i"
| "s_at (SEventually i _) = i"
| "s_at (SHistorically i _ _) = i"
| "s_at (SHistoricallyOut i) = i"
| "s_at (SAlways i _ _) = i"
| "s_at (SSince sp2 sp1s) = (case sp1s of [] \<Rightarrow> s_at sp2 | _ \<Rightarrow> s_at (last sp1s))"
| "s_at (SUntil sp1s sp2) = (case sp1s of [] \<Rightarrow> s_at sp2 | sp1 # _ \<Rightarrow> s_at sp1)"
| "v_at (VFF i) = i"
| "v_at (VPred i _ _) = i"
| "v_at (VEq_Const i _ _) = i"
| "v_at (VNeg sp) = s_at sp"
| "v_at (VOr vp1 _) = v_at vp1"
| "v_at (VAndL vp1) = v_at vp1"
| "v_at (VAndR vp2) = v_at vp2"
| "v_at (VImp sp1 _) = s_at sp1"
| "v_at (VIffSV sp1 _) = s_at sp1"
| "v_at (VIffVS vp1 _) = v_at vp1"
| "v_at (VExists _ part) = v_at (part_hd part)"
| "v_at (VForall _ _ vp1) = v_at vp1"
| "v_at (VPrev vp) = v_at vp + 1"
| "v_at (VPrevZ) = 0"
| "v_at (VPrevOutL i) = i"
| "v_at (VPrevOutR i) = i"
| "v_at (VNext vp) = v_at vp - 1"
| "v_at (VNextOutL i) = i"
| "v_at (VNextOutR i) = i"
| "v_at (VOnceOut i) = i"
| "v_at (VOnce i _ _) = i"
| "v_at (VEventually i _ _) = i"
| "v_at (VHistorically i _) = i"
| "v_at (VAlways i _) = i"
| "v_at (VSinceOut i) = i"
| "v_at (VSince i _ _) = i"
| "v_at (VSinceInf i _ _) = i"
| "v_at (VUntil i _ _) = i"
| "v_at (VUntilInf i _ _) = i"

lift_definition trivial_part :: "'pt \<Rightarrow> ('d, 'pt) part" is "\<lambda>pt. [(UNIV, pt)]"
  by (simp add: partition_on_space)

lemma part_hd_trivial[simp]: "part_hd (trivial_part pt) = pt"
  unfolding part_hd_def
  by (transfer) simp

lemma SubsVals_trivial[simp]: "SubsVals (trivial_part pt) = {(UNIV, pt)}"
  unfolding SubsVals_def
  by (transfer) simp

end