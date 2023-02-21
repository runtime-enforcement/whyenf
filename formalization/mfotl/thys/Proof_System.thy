(*<*)
theory Proof_System
  imports MFOTL "HOL-Library.Disjoint_Sets" "Deriving.Comparator_Generator" "Containers.Collection_Order" "Containers.Set_Impl"
begin
(*>*)

context begin

section \<open>Proof System\<close>

subsection \<open>Time-stamp-time-point Conversion\<close>

definition ETP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat"  where
  "ETP \<sigma> ts = (LEAST i. \<tau> \<sigma> i \<ge> ts)"

definition LTP:: "'a trace \<Rightarrow> nat \<Rightarrow> nat" where
  "LTP \<sigma> ts = Max {i. (\<tau> \<sigma> i) \<le> ts}"

abbreviation "\<delta> \<sigma> i j \<equiv> (\<tau> \<sigma> i - \<tau> \<sigma> j)"

abbreviation "ETP_p \<sigma> i b \<equiv> ETP \<sigma> ((\<tau> \<sigma> i) - b)"
abbreviation "LTP_p \<sigma> i I \<equiv> min i (LTP \<sigma> ((\<tau> \<sigma> i) - left I))"
abbreviation "ETP_f \<sigma> i I \<equiv> max i (ETP \<sigma> ((\<tau> \<sigma> i) + left I))"
abbreviation "LTP_f \<sigma> i b \<equiv> LTP \<sigma> ((\<tau> \<sigma> i) + b)"

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

lemma i_LTP_tau:
  assumes n_asm: "n \<ge> \<tau> \<sigma> 0"
  shows "(i \<le> LTP \<sigma> n \<longleftrightarrow> \<tau> \<sigma> i \<le> n)"
proof
  define A and j where A_def: "A \<equiv> {i. \<tau> \<sigma> i \<le> n}" and j_def: "j \<equiv> LTP \<sigma> n"
  assume P: "i \<le> LTP \<sigma> n"
  from n_asm A_def have A_ne: "A \<noteq> {}" by auto
  from j_def have i_j: "\<tau> \<sigma> i \<le> \<tau> \<sigma> j" using P by auto
  have fin_A: "finite A"
    unfolding A_def
    apply transfer
    apply (simp only: le_eq_less_or_eq)
    apply (simp only: Collect_disj_eq)
    sorry
  from A_ne j_def have "\<tau> \<sigma> j \<le> n"
    using Max_in[of A] A_def fin_A 
    unfolding LTP_def 
    by simp
  then show "\<tau> \<sigma> i \<le> n" using i_j by auto
next
  define A and j where A_def: "A \<equiv> {i. \<tau> \<sigma> i \<le> n}" and j_def: "j \<equiv> LTP \<sigma> n"
  assume Q: "\<tau> \<sigma> i \<le> n" 
  then have "i \<in> A" using A_def by auto
  moreover have "finite A"
    sorry
  ultimately show "i \<le> LTP \<sigma> n" 
    using Max_ge[of A] A_def 
    unfolding LTP_def
    by auto
qed

lemma ETP_delta: "i \<ge> ETP \<sigma> (\<tau> \<sigma> l + n) \<Longrightarrow> \<delta> \<sigma> i l \<ge> n"
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

subsection \<open>Soundness and Completeness\<close>

inductive SAT and VIO :: "'a MFOTL.trace \<Rightarrow> 'a MFOTL.env \<Rightarrow> nat \<Rightarrow> 'a MFOTL.formula \<Rightarrow> bool" for \<sigma> where
  STT: "SAT \<sigma> v i MFOTL.TT"
| VFF: "VIO \<sigma> v i MFOTL.FF"
| SPred: "(r, MFOTL.eval_trms v ts) \<in> \<Gamma> \<sigma> i \<Longrightarrow> SAT \<sigma> v i (MFOTL.Pred r ts)"
| VPred: "(r, MFOTL.eval_trms v ts) \<notin> \<Gamma> \<sigma> i \<Longrightarrow> VIO \<sigma> v i (MFOTL.Pred r ts)"
| SNeg: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Neg \<phi>)"
| VNeg: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Neg \<phi>)"
| SOrL: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Or \<phi> \<psi>)"
| SOrR: "SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Or \<phi> \<psi>)"
| VOr: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Or \<phi> \<psi>)"
| SAnd: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.And \<phi> \<psi>)"
| VAndL: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.And \<phi> \<psi>)"
| VAndR: "VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.And \<phi> \<psi>)"
| SImpL: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Imp \<phi> \<psi>)"
| SImpR: "SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Imp \<phi> \<psi>)"
| VImp: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Imp \<phi> \<psi>)"
| SIffSS: "SAT \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Iff \<phi> \<psi>)"
| SIffVV: "VIO \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Iff \<phi> \<psi>)"
| VIffSV: "SAT \<sigma> v i \<phi> \<Longrightarrow> VIO \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Iff \<phi> \<psi>)"
| VIffVS: "VIO \<sigma> v i \<phi> \<Longrightarrow> SAT \<sigma> v i \<psi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Iff \<phi> \<psi>)"
| SExists: "\<exists>z. SAT \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Exists x \<phi>)"
| VExists: "\<forall>z. VIO \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Exists x \<phi>)"
| SForall: "\<forall>z. SAT \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Forall x \<phi>)"
| VForall: "\<exists>z. VIO \<sigma> (v (x := z)) i \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Forall x \<phi>)"
| SPrev: "i > 0 \<Longrightarrow> mem (\<Delta> \<sigma> i) I \<Longrightarrow> SAT \<sigma> v (i-1) \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Prev I \<phi>)"
| VPrev: "i > 0 \<Longrightarrow> VIO \<sigma> v (i-1) \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Prev I \<phi>)"
| VPrevZ: "i = 0 \<Longrightarrow> VIO \<sigma> v i (MFOTL.Prev I \<phi>)"
| VPrevOutL: "i > 0 \<Longrightarrow> (\<Delta> \<sigma> i) < (left I) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Prev I \<phi>)"
| VPrevOutR: "i > 0 \<Longrightarrow> enat (\<Delta> \<sigma> i) > (right I) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Prev I \<phi>)"
| SNext: "mem (\<Delta> \<sigma> (i+1)) I \<Longrightarrow> SAT \<sigma> v (i+1) \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Next I \<phi>)"
| VNext: "VIO \<sigma> v (i+1) \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Next I \<phi>)"
| VNextOutL: "(\<Delta> \<sigma> (i+1)) < (left I) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Next I \<phi>)"
| VNextOutR: "enat (\<Delta> \<sigma> (i+1)) > (right I) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Next I \<phi>)"
| SOnce: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I \<Longrightarrow> SAT \<sigma> v j \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Once I \<phi>)"
| VOnceOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> VIO \<sigma> v i (MFOTL.Once I \<phi>)"
| VOnce: "j = (case right I of \<infinity> \<Rightarrow> 0 
               | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
          (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow>
          (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> VIO \<sigma> v k \<phi>) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Once I \<phi>)"
| SEventually: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> SAT \<sigma> v j \<phi> \<Longrightarrow> SAT \<sigma> v i (MFOTL.Eventually I \<phi>)"
| VEventually: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..}
                           | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> VIO \<sigma> v k \<phi>) \<Longrightarrow> 
                VIO \<sigma> v i (MFOTL.Eventually I \<phi>)"
| SHistorically: "j = (case right I of \<infinity> \<Rightarrow> 0
                       | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
                 (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow>
                 (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow> SAT \<sigma> v i (MFOTL.Historically I \<phi>)"
| SHistoricallyOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> SAT \<sigma> v i (MFOTL.Historically I \<phi>)"
| VHistorically: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I  \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Historically I \<phi>)"
| SAlways: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..} 
                       | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow>
            SAT \<sigma> v i (MFOTL.Always I \<phi>)"
| VAlways: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> VIO \<sigma> v i (MFOTL.Always I \<phi>)"
| SSince: "j \<le> i \<Longrightarrow> mem (\<delta> \<sigma> i j) I  \<Longrightarrow> SAT \<sigma> v j \<psi> \<Longrightarrow> (\<And>k. k \<in> {j <.. i} \<Longrightarrow> 
           SAT \<sigma> v k \<phi>) \<Longrightarrow> SAT \<sigma> v i (MFOTL.Since \<phi> I \<psi>)"
| VSinceOut: "\<tau> \<sigma> i < \<tau> \<sigma> 0 + left I \<Longrightarrow> VIO \<sigma> v i (MFOTL.Since \<phi> I \<psi>)"
| VSince: "(case right I of \<infinity> \<Rightarrow> True 
            | enat b \<Rightarrow> ETP \<sigma> ((\<tau> \<sigma> i) - b) \<le> j) \<Longrightarrow> 
           j \<le> i \<Longrightarrow> (\<tau> \<sigma> 0) + left I \<le> (\<tau> \<sigma> i) \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow>
           (\<And>k. k \<in> {j .. (LTP_p \<sigma> i I)} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Since \<phi> I \<psi>)"
| VSinceInf: "j = (case right I of \<infinity> \<Rightarrow> 0 
                   | enat b \<Rightarrow> ETP_p \<sigma> i b) \<Longrightarrow>
             (\<tau> \<sigma> i) \<ge> (\<tau> \<sigma> 0) + left I \<Longrightarrow> 
             (\<And>k. k \<in> {j .. LTP_p \<sigma> i I} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> VIO \<sigma> v i (MFOTL.Since \<phi> I \<psi>)"
| SUntil: "j \<ge> i \<Longrightarrow> mem (\<delta> \<sigma> j i) I  \<Longrightarrow> SAT \<sigma> v j \<psi> \<Longrightarrow> (\<And>k. k \<in> {i ..< j} \<Longrightarrow> SAT \<sigma> v k \<phi>) \<Longrightarrow> 
           SAT \<sigma> v i (MFOTL.Until \<phi> I \<psi>)"
| VUntil: "(case right I of \<infinity> \<Rightarrow> True 
            | enat b \<Rightarrow> j \<le> LTP_f \<sigma> i b) \<Longrightarrow> 
           j \<ge> i \<Longrightarrow> VIO \<sigma> v j \<phi> \<Longrightarrow> (\<And>k. k \<in> {ETP_f \<sigma> i I .. j} \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow> 
           VIO \<sigma> v i (MFOTL.Until \<phi> I \<psi>)"
| VUntilInf: "(\<And>k. k \<in> (case right I of \<infinity> \<Rightarrow> {ETP_f \<sigma> i I ..} 
                         | enat b \<Rightarrow> {ETP_f \<sigma> i I .. LTP_f \<sigma> i b}) \<Longrightarrow> VIO \<sigma> v k \<psi>) \<Longrightarrow>
              VIO \<sigma> v i (MFOTL.Until \<phi> I \<psi>)"

lemma soundness: "(SAT \<sigma> v i \<phi> \<longrightarrow> MFOTL.sat \<sigma> v i \<phi>) \<and> (VIO \<sigma> v i \<phi> \<longrightarrow> \<not> MFOTL.sat \<sigma> v i \<phi>)"
proof (induct v i \<phi> rule: SAT_VIO.induct)
  case (SPrev i I v \<phi>)
  then show ?case sorry
next
  case (VPrev i v \<phi> I)
  then show ?case sorry
next
  case (VPrevZ i v I \<phi>)
  then show ?case sorry
next
  case (VPrevOutL i I v \<phi>)
  then show ?case sorry
next
  case (VPrevOutR i I v \<phi>)
  then show ?case sorry
next
  case (SNext i I v \<phi>)
  then show ?case sorry
next
  case (VNext v i \<phi> I)
  then show ?case sorry
next
  case (VNextOutL i I v \<phi>)
  then show ?case sorry
next
  case (VNextOutR i I v \<phi>)
  then show ?case sorry
next
  case (SOnce j i I v \<phi>)
  then show ?case sorry
next
  case (VOnceOut i I v \<phi>)
  then show ?case sorry
next
  case (VOnce j I i v \<phi>)
  then show ?case sorry
next
  case (SEventually j i I v \<phi>)
  then show ?case sorry
next
  case (VEventually I i v \<phi>)
  then show ?case sorry
next
  case (SHistorically j I i v \<phi>)
  then show ?case sorry
next
  case (SHistoricallyOut i I v \<phi>)
  then show ?case sorry
next
  case (VHistorically j i I v \<phi>)
  then show ?case sorry
next
  case (SAlways I i v \<phi>)
  then show ?case sorry
next
  case (VAlways j i I v \<phi>)
  then show ?case sorry
next
  case (VSinceOut i I v \<phi> \<psi>)
  then show ?case sorry
next
  case (VSince I i j v \<phi> \<psi>)
  then show ?case sorry
next
  case (VSinceInf j I i v \<psi> \<phi>)
  then show ?case sorry
next
  case (VUntil I j i v \<phi> \<psi>)
  then show ?case sorry
next
  case (VUntilInf I i v \<psi> \<phi>)
  then show ?case sorry
qed (auto simp: fun_upd_def)

lemma completeness: "(MFOTL.sat \<sigma> v i \<phi> \<longrightarrow> SAT \<sigma> v i \<phi>) \<and> (\<not> MFOTL.sat \<sigma> v i \<phi> \<longrightarrow> VIO \<sigma> v i \<phi>)"
proof (induct \<phi> arbitrary: i v)
  case (Prev x1 \<phi>)
  then show ?case sorry
next
  case (Next x1 \<phi>)
  then show ?case sorry
next
  case (Once x1 \<phi>)
  then show ?case sorry
next
  case (Historically x1 \<phi>)
  then show ?case sorry
next
  case (Eventually x1 \<phi>)
  then show ?case sorry
next
  case (Always x1 \<phi>)
  then show ?case sorry
next
  case (Since \<phi>1 x2 \<phi>2)
  then show ?case sorry
next
  case (Until \<phi>1 x2 \<phi>2)
  then show ?case sorry
qed (auto intro: SAT_VIO.intros)

lemma SAT_or_VIO: "SAT \<sigma> v i \<phi> \<or> VIO \<sigma> v i \<phi>"
  using completeness by auto

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

lift_bnf (no_warn_wits, no_warn_transfer) (dead 'd, 'a) part
  unfolding part_list_set_eq[symmetric]
  by (auto simp: image_iff)

subsection \<open>\<^const>\<open>size\<close> setup\<close>

lift_definition subs :: "('d, 'a) part \<Rightarrow> 'd set list" is "map fst" .

lift_definition Subs :: "('d, 'a) part \<Rightarrow> 'd set set" is "set o map fst" .

lift_definition vals :: "('d, 'a) part \<Rightarrow> 'a list" is "map snd" .

lift_definition Vals :: "('d, 'a) part \<Rightarrow> 'a set" is "set o map snd" .

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

lemma set_vals[simp]: "set (vals xs) = Vals xs"
  by transfer simp

subsection \<open>Proof Objects\<close>

datatype (dead 'd) sproof = STT nat 
  | SPred nat MFOTL.name "'d MFOTL.trm list" 
  | SNeg "'d vproof" 
  | SOrL "'d sproof" 
  | SOrR "'d sproof" 
  | SAnd "'d sproof" "'d sproof"
  | SImpL "'d vproof" 
  | SImpR "'d sproof"
  | SIffSS "'d sproof" "'d sproof" 
  | SIffVV "'d vproof" "'d vproof" 
  | SExists MFOTL.name 'd "'d sproof"
  | SForall MFOTL.name "('d, 'd sproof) part" 
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
  | VPred nat MFOTL.name "'d MFOTL.trm list" 
  | VNeg "'d sproof" 
  | VOr "'d vproof" "'d vproof"
  | VAndL "'d vproof" 
  | VAndR "'d vproof" 
  | VImp "'d sproof" "'d vproof" 
  | VIffSV "'d sproof" "'d vproof" 
  | VIffVS "'d vproof" "'d sproof" 
  | VExists MFOTL.name "('d, 'd vproof) part" 
  | VForall MFOTL.name 'd "'d vproof"
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
datatype ('d, 'pt) pdt = Leaf (unleaf: 'pt) | Node MFOTL.name "('d, ('d, 'pt) pdt) part"

type_synonym 'd "proof" = "'d sproof + 'd vproof"

type_synonym 'd expl = "('d, 'd proof) pdt"

fun vars_expl :: "'d expl \<Rightarrow> MFOTL.name set" where
  "vars_expl (Node x part) = {x} \<union> (\<Union>pdt \<in> Vals part. vars_expl pdt)"
| "vars_expl (Leaf pt) = {}"

fun merge_part_raw :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('d set \<times> 'a) list \<Rightarrow> ('d set \<times> 'a) list \<Rightarrow> ('d set \<times> 'a) list" where
  "merge_part_raw f [] part2 = part2"  
| "merge_part_raw f ((P1, v1) # part1) part2 = 
    (let part12 = List.map_filter (\<lambda>(P2, v2). if P1 \<inter> P2 \<noteq> {} then Some(P1 \<inter> P2, f v1 v2) else None) part2 in
     let part2not1 = List.map_filter (\<lambda>(P2, v2). if P2 - P1 \<noteq> {} then Some(P2 - P1, v2) else None) part2 in
     part12 @ (merge_part_raw f part1 part2not1))"

lemma partition_on_empty_iff: 
  "partition_on X \<P> \<Longrightarrow> \<P> = {} \<longleftrightarrow> X = {}"
  "partition_on X \<P> \<Longrightarrow> \<P> \<noteq> {} \<longleftrightarrow> X \<noteq> {}"
  by (auto simp: partition_on_def)

lemma wf_part_list_filter_inter: 
  defines "inP1 P1 f v1 part2 
    \<equiv> List.map_filter (\<lambda>(P2, v2). if P1 \<inter> P2 \<noteq> {} then Some(P1 \<inter> P2, f v1 v2) else None) part2"
  assumes "partition_on X (set (map fst ((P1, v1) # part1)))"
    and "partition_on X (set (map fst part2))"
  shows "partition_on P1 (set (map fst (inP1 P1 f v1 part2)))"
    and "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst (part2)) 
      \<Longrightarrow> distinct (map fst (inP1 P1 f v1 part2))"
proof (rule partition_onI)
  show "\<Union> (set (map fst (inP1 P1 f v1 part2))) = P1"
    using partition_onD1[OF assms(2)] partition_onD1[OF assms(3)] inP1_def
    by (auto simp: map_filter_def split: if_splits)
      (metis (no_types, lifting) Int_iff UN_iff Un_Int_eq(3) empty_iff prod.collapse)
  show "\<And>A1 A2. A1 \<in> set (map fst (inP1 P1 f v1 part2)) 
    \<Longrightarrow> A2 \<in> set (map fst (inP1 P1 f v1 part2)) \<Longrightarrow> A1 \<noteq> A2 \<Longrightarrow> disjnt A1 A2" 
    using partition_onD2[OF assms(2)] partition_onD2[OF assms(3)] inP1_def
    by (clarsimp simp: disjnt_def map_filter_def disjoint_def split: if_splits)
      (smt (verit, del_insts) Int_assoc Int_commute fst_conv inf_bot_right)
  show "{} \<notin> set (map fst (inP1 P1 f v1 part2))" 
    using assms
    by (auto simp: map_filter_def split: if_splits)
  show "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst part2) 
    \<Longrightarrow> distinct (map fst (inP1 P1 f v1 part2))"
    using partition_onD2[OF assms(3), unfolded disjoint_def] distinct_map[of fst part2]
    by (clarsimp simp: inP1_def map_filter_def distinct_map inj_on_def split: prod.splits)
      (metis Int_assoc fst_conv inf.idem inf_bot_right prod.inject)
qed

lemma wf_part_list_filter_minus: 
  defines "notinP2 P1 f v1 part2 
    \<equiv> List.map_filter (\<lambda>(P2, v2). if P2 - P1 \<noteq> {} then Some(P2 - P1, v2) else None) part2"
  assumes "partition_on X (set (map fst ((P1, v1) # part1)))"
    and "partition_on X (set (map fst part2))"
  shows "partition_on (X - P1) (set (map fst (notinP2 P1 f v1 part2)))"
    and "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst (part2)) 
      \<Longrightarrow> distinct (map fst (notinP2 P1 f v1 part2))"
proof (rule partition_onI)
  show "\<Union> (set (map fst (notinP2 P1 f v1 part2))) = X - P1"
    using partition_onD1[OF assms(2)] partition_onD1[OF assms(3)] notinP2_def
    apply (intro set_eqI iffI; clarsimp simp: map_filter_def subset_eq split: if_splits)
    by (metis (no_types, lifting) UN_iff Un_iff fst_conv prod.collapse)+
  show "\<And>A1 A2. A1 \<in> set (map fst (notinP2 P1 f v1 part2)) 
    \<Longrightarrow> A2 \<in> set (map fst (notinP2 P1 f v1 part2)) \<Longrightarrow> A1 \<noteq> A2 \<Longrightarrow> disjnt A1 A2" 
    using partition_onD2[OF assms(2)] partition_onD2[OF assms(3)] notinP2_def
    by (clarsimp simp: disjnt_def map_filter_def disjoint_def split: if_splits)
      (smt (verit, ccfv_SIG) Diff_disjoint Int_Diff Int_commute fst_conv)
  show "{} \<notin> set (map fst (notinP2 P1 f v1 part2))" 
    using assms
    by (auto simp: map_filter_def split: if_splits)
  show "distinct (map fst ((P1, v1) # part1)) \<Longrightarrow> distinct (map fst part2) 
    \<Longrightarrow> distinct (map fst ((notinP2 P1 f v1 part2)))"
    using partition_onD2[OF assms(3), unfolded disjoint_def] distinct_map[of fst part2]
    by (clarsimp simp: notinP2_def map_filter_def distinct_map inj_on_def split: prod.splits)
      (metis Diff_Diff_Int Diff_empty Diff_iff fst_conv prod.inject)
qed

lemma wf_part_list_tail: 
  assumes "partition_on X (set (map fst ((P1, v1) # part1)))"
    and "distinct (map fst ((P1, v1) # part1))"
  shows "partition_on (X - P1) (set (map fst part1))"
    and "distinct (map fst part1)"
proof (rule partition_onI)
  show "\<Union> (set (map fst part1)) = X - P1"
    using partition_onD1[OF assms(1)] partition_onD2[OF assms(1)] assms(2)
    by (auto simp: disjoint_def image_iff)
  show "\<And>A1 A2. A1 \<in> set (map fst part1) \<Longrightarrow> A2 \<in> set (map fst part1) \<Longrightarrow> A1 \<noteq> A2 \<Longrightarrow> disjnt A1 A2" 
    using partition_onD2[OF assms(1)]
    by (clarsimp simp: disjnt_def disjoint_def)
      (smt (verit, ccfv_SIG) Diff_disjoint Int_Diff Int_commute fst_conv)
  show "{} \<notin> set (map fst part1)" 
    using partition_onD3[OF assms(1)]
    by (auto simp: map_filter_def split: if_splits)
  show "distinct (map fst (part1))"
    using assms(2)
    by auto
qed

lemma partition_on_append: "partition_on X (set xs) \<Longrightarrow> partition_on Y (set ys) 
  \<Longrightarrow> X \<inter> Y = {} \<Longrightarrow> partition_on (X \<union> Y) (set (xs @ ys))"
  by (auto simp: partition_on_def disjoint_def)
    (metis disjoint_iff)+

lemma wf_part_list_merge_part_raw: 
  "partition_on X (set (map fst part1)) \<and> distinct (map fst part1) 
  \<Longrightarrow> partition_on X (set (map fst part2)) \<and> distinct (map fst part2) 
  \<Longrightarrow> partition_on X (set (map fst (merge_part_raw f part1 part2))) 
    \<and> distinct (map fst (merge_part_raw f part1 part2))"
proof(induct f part1 part2 arbitrary: X rule: merge_part_raw.induct)
  case (2 f P1 v1 part1 part2)
  let ?inP1 = "List.map_filter (\<lambda>(P2, v2). if P1 \<inter> P2 \<noteq> {} then Some (P1 \<inter> P2, f v1 v2) else None) part2"
    and ?notinP1 = "List.map_filter (\<lambda>(P2, v2). if P2 - P1 \<noteq> {} then Some (P2 - P1, v2) else None) part2"
  have "P1 \<union> X = X"
    using "2.prems"
    by (auto simp: partition_on_def)
  have wf_part1: "partition_on (X - P1) (set (map fst part1))"
    "distinct (map fst part1)"
    using wf_part_list_tail "2.prems" by auto
  moreover have wf_notinP1: "partition_on (X - P1) (set (map fst ?notinP1))" 
    "distinct (map fst (?notinP1))"
    using wf_part_list_filter_minus[OF 2(2)[THEN conjunct1]] 
      "2.prems" by auto
  ultimately have IH: "partition_on (X - P1) (set (map fst (merge_part_raw f part1 (?notinP1))))"
    "distinct (map fst (merge_part_raw f part1 (?notinP1)))"
    using "2.hyps"[OF refl refl] by auto
  moreover have wf_inP1: "partition_on P1 (set (map fst ?inP1))" "distinct (map fst ?inP1)"
    using wf_part_list_filter_inter[OF 2(2)[THEN conjunct1]]
      "2.prems" by auto
  moreover have "(fst ` set ?inP1) \<inter> (fst ` set (merge_part_raw f part1 (?notinP1))) = {}"
    using IH(1)[THEN partition_onD1]
    by (intro set_eqI iffI; clarsimp simp: map_filter_def split: prod.splits if_splits)
      (smt (z3) Diff_disjoint Int_iff UN_iff disjoint_iff fst_conv)+
  ultimately show ?case 
    using partition_on_append[OF wf_inP1(1) IH(1)] \<open>P1 \<union> X = X\<close> wf_inP1(2) IH(2)
    by simp
qed simp

lift_definition merge_part :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('d, 'a) part \<Rightarrow> ('d, 'a) part \<Rightarrow> ('d, 'a) part" is merge_part_raw
  by (rule wf_part_list_merge_part_raw)               

subsection \<open>Comparator\<close>

(* This is needed because of primrec requirements *)
context fixes compa :: "'a \<Rightarrow> 'b \<Rightarrow> order" begin

fun comparator_list' :: "'a list \<Rightarrow> 'b list \<Rightarrow> order" where
  "comparator_list' [] [] = Eq"
| "comparator_list' [] (y # ys) = Lt"
| "comparator_list' (x # xs) [] = Gt"
| "comparator_list' (x # xs) (y # ys) = (case compa x y of Eq \<Rightarrow> comparator_list' xs ys | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)"

end

definition comparator_set where
  "comparator_set compa = comp_of_ords (ord.set_less_eq (le_of_comp compa)) (ord.set_less (le_of_comp compa))"

derive ccompare MFOTL.trm

term "subsvals (map_part ((comparator_sproof::('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> 'a sproof \<Rightarrow> 'a sproof \<Rightarrow> order) compa) part)"

instantiation sproof and vproof :: (ccompare) ccompare 
begin

primrec comparator_sproof :: "('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> 'a sproof \<Rightarrow> 'a sproof \<Rightarrow> order" 
  and comparator_vproof :: "('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> 'a vproof \<Rightarrow> 'a vproof \<Rightarrow> order" where
  "comparator_sproof compa (STT i) rhs =
    (case rhs of       
      STT i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SPred i r ts) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred i' r' ts' \<Rightarrow> (case comparator_of i i' of
                           Eq \<Rightarrow> (case compare r r' of
                                   Eq \<Rightarrow> comparator_list (comparator_trm compa) ts ts'
                                 | Lt \<Rightarrow> Lt
                                 | Gt \<Rightarrow> Gt)
                         | Lt \<Rightarrow> Lt
                         | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SNeg vp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SOrL sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SOrR sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SAnd sp1 sp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd sp1' sp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of 
                          Eq \<Rightarrow> comparator_sproof compa sp2 sp2' 
                        | Lt \<Rightarrow> Lt 
                        | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SImpL vp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SImpR sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SIffSS sp1 sp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS sp1' sp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of 
                            Eq \<Rightarrow> comparator_sproof compa sp2 sp2' 
                          | Lt \<Rightarrow> Lt
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SIffVV vp1 vp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV vp1' vp2' \<Rightarrow> (case comparator_vproof compa vp1 vp1' of 
                            Eq \<Rightarrow> comparator_vproof compa vp2 vp2'   
                          | Lt \<Rightarrow> Lt 
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SExists x val sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists x' val' sp' \<Rightarrow> (case compare x x' of
                               Eq \<Rightarrow> (case compa val val' of
                                       Eq \<Rightarrow> comparator_sproof compa sp sp'
                                     | Lt \<Rightarrow> Lt
                                     | Gt \<Rightarrow> Gt)
                             | Lt \<Rightarrow> Lt
                             | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SForall x part) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall x' part' \<Rightarrow> (case compare x x' of 
                            Eq \<Rightarrow> comparator_list' (\<lambda>(A,f) (B,x). case comparator_set compa A B of 
                                                                   Eq \<Rightarrow> f x
                                                                 | Lt \<Rightarrow> Lt
                                                                 | Gt \<Rightarrow> Gt)
                                 (subsvals (map_part (comparator_sproof compa) part)) (subsvals part')
                          | Lt \<Rightarrow> Lt
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SPrev sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev sp' \<Rightarrow> comparator_sproof compa sp sp' 
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SNext sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext sp' \<Rightarrow> comparator_sproof compa sp sp' 
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SOnce i sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce i' sp' \<Rightarrow> (case comparator_of i i' of 
                        Eq \<Rightarrow> comparator_sproof compa sp sp' 
                      | Lt \<Rightarrow> Lt 
                      | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SEventually i sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually i' sp' \<Rightarrow> (case comparator_of i i' of 
                              Eq \<Rightarrow> comparator_sproof compa sp sp' 
                            | Lt \<Rightarrow> Lt 
                            | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SHistorically i li sps) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually _ _ \<Rightarrow> Gt
    | SHistorically i' li' sps' \<Rightarrow> (case comparator_of i i' of 
                                     Eq \<Rightarrow> (case comparator_of li li' of 
                                             Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_sproof compa) sps) sps'
                                           | Lt \<Rightarrow> Lt 
                                           | Gt \<Rightarrow> Gt)
                                   | Lt \<Rightarrow> Lt 
                                   | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SHistoricallyOut i) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually _ _ \<Rightarrow> Gt
    | SHistorically _ _ _ \<Rightarrow> Gt
    | SHistoricallyOut i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SAlways i hi sps) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually _ _ \<Rightarrow> Gt
    | SHistorically _ _ _ \<Rightarrow> Gt
    | SHistoricallyOut _ \<Rightarrow> Gt
    | SAlways i' hi' sps' \<Rightarrow> (case comparator_of i i' of 
                               Eq \<Rightarrow> (case comparator_of hi hi' of 
                                       Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_sproof compa) sps) sps'
                                     | Lt \<Rightarrow> Lt 
                                     | Gt \<Rightarrow> Gt)
                             | Lt \<Rightarrow> Lt 
                             | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SSince sp2 sp1s) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually _ _ \<Rightarrow> Gt
    | SHistorically _ _ _ \<Rightarrow> Gt
    | SHistoricallyOut _ \<Rightarrow> Gt
    | SAlways _ _ _ \<Rightarrow> Gt
    | SSince sp2' sp1s' \<Rightarrow> (case comparator_sproof compa sp2 sp2' of 
                             Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_sproof compa) sp1s) sp1s'
                           | Lt \<Rightarrow> Lt 
                           | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SUntil sp1s sp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually _ _ \<Rightarrow> Gt
    | SHistorically _ _ _ \<Rightarrow> Gt
    | SHistoricallyOut _ \<Rightarrow> Gt
    | SAlways _ _ _ \<Rightarrow> Gt
    | SSince _ _ \<Rightarrow> Gt
    | SUntil sp1s' sp2' \<Rightarrow> (case comparator_sproof compa sp2 sp2' of 
                             Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_sproof compa) sp1s) sp1s'
                           | Lt \<Rightarrow> Lt 
                           | Gt \<Rightarrow> Gt))"
| "comparator_vproof compa (VFF i) rhs =
    (case rhs of
      VFF i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VPred i r ts) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred i' r' ts' \<Rightarrow> (case comparator_of i i' of
                           Eq \<Rightarrow> (case compare r r' of
                                   Eq \<Rightarrow> comparator_list (comparator_trm compa) ts ts'
                                 | Lt \<Rightarrow> Lt
                                 | Gt \<Rightarrow> Gt)
                         | Lt \<Rightarrow> Lt
                         | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VNeg sp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VOr vp1 vp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr vp1' vp2' \<Rightarrow> (case comparator_vproof compa vp1 vp1' of 
                         Eq \<Rightarrow> comparator_vproof compa vp2 vp2' 
                       | Lt \<Rightarrow> Lt 
                       | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VAndL vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VAndR vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VImp sp1 vp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp sp1' vp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of 
                          Eq \<Rightarrow> comparator_vproof compa vp2 vp2' 
                        | Lt \<Rightarrow> Lt 
                        | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VIffSV sp1 vp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV sp1' vp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of 
                            Eq \<Rightarrow> comparator_vproof compa vp2 vp2' 
                          | Lt \<Rightarrow> Lt 
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VIffVS vp1 sp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS vp1' sp2' \<Rightarrow> (case comparator_vproof compa vp1 vp1' of 
                            Eq \<Rightarrow> comparator_sproof compa sp2 sp2' 
                          | Lt \<Rightarrow> Lt 
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VExists x part) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists x' part' \<Rightarrow> (case compare x x' of 
                            Eq \<Rightarrow> comparator_list' undefined (vals (map_part (comparator_vproof compa) part)) (vals part')
                          | Lt \<Rightarrow> Lt
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VForall x val vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall x' val' vp' \<Rightarrow> (case compare x x' of
                               Eq \<Rightarrow> (case compa val val' of
                                       Eq \<Rightarrow> comparator_vproof compa vp vp'
                                     | Lt \<Rightarrow> Lt
                                     | Gt \<Rightarrow> Gt)
                             | Lt \<Rightarrow> Lt
                             | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VPrev vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa VPrevZ rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Eq
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VPrevOutL i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VPrevOutR i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"

| "comparator_vproof compa (VNext vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VNextOutL i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VNextOutR i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VOnceOut i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VOnce i li vps) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce i' li' vps' \<Rightarrow> (case comparator_of i i' of 
                             Eq \<Rightarrow> (case comparator_of li li' of 
                                     Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vps) vps' 
                                   | Lt \<Rightarrow> Lt 
                                   | Gt \<Rightarrow> Gt)
                           | Lt \<Rightarrow> Lt 
                           | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VEventually i hi vps) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually i' hi' vps' \<Rightarrow> (case comparator_of i i' of 
                                   Eq \<Rightarrow> (case comparator_of hi hi' of 
                                           Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vps) vps'
                                         | Lt \<Rightarrow> Lt 
                                         | Gt \<Rightarrow> Gt)
                                 | Lt \<Rightarrow> Lt 
                                 | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VHistorically i vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically i' vp' \<Rightarrow> (case comparator_of i i' of 
                                Eq \<Rightarrow> comparator_vproof compa vp vp' 
                              | Lt \<Rightarrow> Lt 
                              | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VAlways i vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways i' vp' \<Rightarrow> (case comparator_of i i' of 
                          Eq \<Rightarrow> comparator_vproof compa vp vp' 
                        | Lt \<Rightarrow> Lt 
                        | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VSinceOut i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways _ _ \<Rightarrow> Gt
    | VSinceOut i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VSince i vp1 vp2s) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways _ _ \<Rightarrow> Gt
    | VSinceOut _ \<Rightarrow> Gt
    | VSince i' vp1' vp2s' \<Rightarrow> (case comparator_of i i' of 
                                Eq \<Rightarrow> (case comparator_vproof compa vp1 vp1' of
                                        Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s'
                                      | Lt \<Rightarrow> Lt 
                                      | Gt \<Rightarrow> Gt)
                              | Lt \<Rightarrow> Lt 
                              | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VSinceInf i li vp2s) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways _ _ \<Rightarrow> Gt
    | VSinceOut _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VSinceInf i' li' vp2s' \<Rightarrow> (case comparator_of i i' of 
                                  Eq \<Rightarrow> (case comparator_of li li' of 
                                          Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s'
                                        | Lt \<Rightarrow> Lt 
                                        | Gt \<Rightarrow> Gt)
                                | Lt \<Rightarrow> Lt 
                                | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VUntil i vp2s vp1) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways _ _ \<Rightarrow> Gt
    | VSinceOut _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VSinceInf _ _ _ \<Rightarrow> Gt
    | VUntil i' vp2s' vp1' \<Rightarrow> (case comparator_of i i' of 
                                Eq \<Rightarrow> (case comparator_vproof compa vp1 vp1' of
                                        Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s'
                                      | Lt \<Rightarrow> Lt 
                                      | Gt \<Rightarrow> Gt)
                              | Lt \<Rightarrow> Lt 
                              | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VUntilInf i hi vp2s) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways _ _ \<Rightarrow> Gt
    | VSinceOut _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VSinceInf _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VUntilInf i' hi' vp2s' \<Rightarrow> (case comparator_of i i' of 
                                  Eq \<Rightarrow> (case comparator_of hi hi' of 
                                          Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s'
                                        | Lt \<Rightarrow> Lt 
                                        | Gt \<Rightarrow> Gt)
                                | Lt \<Rightarrow> Lt 
                                | Gt \<Rightarrow> Gt))"


definition "ccompare_sproof = (case ID ccompare of None \<Rightarrow> None | Some comp_'a \<Rightarrow> Some (comparator_sproof comp_'a))"
definition "ccompare_vproof = (case ID ccompare of None \<Rightarrow> None | Some comp_'a \<Rightarrow> Some (comparator_vproof comp_'a))"

find_theorems name:List.map

thm comparator_list'.induct

definition mycomp where
  "mycomp x y = (if x < y then Lt else (if x > y then Gt else Eq))"

term "comparator_list"

find_consts " _ \<Rightarrow> _ set \<Rightarrow> _ set \<Rightarrow> order"

find_consts name: comparator_set

term "ccompare"

value "the ccompare_set_inst.ccompare_set {1,2} ({2}::nat set)"

value "comparator_list mycomp ([1]::nat list) [1]"

find_theorems name:List.map_append

lemma comparator_list'_map[simp]: "comparator_list' (\<lambda>f x. f x) (map f xs) ys = comparator_list f xs ys"
  by (induct xs ys rule: comparator_list'.induct[where compa = f]) (auto split: order.splits)



lemma comparator_list'_map2[simp]: "comparator_list' (\<lambda>(A,f) (B,x). case comparator_set compa A B of Eq \<Rightarrow> f x | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt) (map (map_prod id f) xs) ys = comparator_list (comparator_prod (comparator_set compa) f) xs ys"
  by (induct xs ys rule: comparator_list'.induct[where compa = "(comparator_prod (comparator_set compa) f)"]) (auto split: order.splits)

lemma comparator_list'_vals_map_part [simp]: "subsvals (map_part f part) = map (map_prod id f) (subsvals part)"
  apply transfer
  apply auto
  done

lemma eq_Eq_comparator_proof:
  assumes "ID ccompare = Some compa"
  shows "(comparator_sproof compa sp sp' = Eq) \<longleftrightarrow> (sp = sp')"
    "(comparator_vproof compa vp vp' = Eq) \<longleftrightarrow> (vp = vp')"
proof (induction sp and vp arbitrary: sp' and vp')
  case (STT x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SPred x1 x2 x3)
  then show ?case
    by (auto simp add: comparator_of_def comparator.eq_Eq_conv ID_ccompare' assms comparator_list comparator_trm 
        split: sproof.splits order.splits)
next
  case (SNeg x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrL x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrR x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAnd x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply force
    done
next
  case (SImpL x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SImpR x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SIffSS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply force
    done
next
  case (SIffVV x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply force
    done
next
  case (SExists x1 x2 x3)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis ID_code assms ccompare comparator.eq_Eq_conv compare_refl order.distinct(1,3))
    done
next
  case (SForall x part)
  (* fix part'
  have sp'_def: "sp' = SForall x part'"
    sorry
  then have "subsp \<in> set_part part \<Longrightarrow> subsp' \<in> set_part part' \<Longrightarrow> (comparator_sproof compa subsp subsp' = Eq) = (subsp = subsp')"
    using SForall
    by simp
  then have "(comparator_sproof compa (SForall x part) sp' = Eq) = (SForall x part = sp')"
    using sp'_def 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    sorry *)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply safe
    thm comparator.eq_Eq_conv ccompare 
    using comparator.eq_Eq_conv[OF ccompare[OF ]]
    sorry
next
  case (SPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SNext x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOnce x1 x2)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SEventually x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SHistorically x1 x2 x3)
  then show ?case
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SHistoricallyOut x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAlways x1 x2 x3)
  then show ?case
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SSince x1 x2)
  then show ?case
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis order.distinct(1) order.distinct(3))
    done
next
  case (SUntil x1 x2)
  then show ?case
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis order.distinct(1) order.distinct(3))
    done
next
  case (VFF x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPred x1 x2 x3)
  then show ?case
    by (auto simp add: comparator_of_def comparator.eq_Eq_conv ID_ccompare' assms comparator_list comparator_trm 
        split: vproof.splits order.splits)
next
  case (VNeg x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOr x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply force
    done
next
  case (VAndL x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAndR x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VImp x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply force
    done
next
  case (VIffSV x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply force
    done
next
  case (VIffVS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply force
    done
next
  case (VExists x1 x2)
  then show ?case sorry
next
  case (VForall x1 x2 x3)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (metis ID_code assms ccompare comparator.eq_Eq_conv compare_refl order.distinct(1) order.distinct(3))
    done
next
  case (VPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case VPrevZ
  then show ?case 
    by (simp split: vproof.splits)
next
  case (VPrevOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPrevOutR x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNext x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnce x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VEventually x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VHistorically x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAlways x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSinceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSince x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.split order.splits)
    apply (metis order.distinct(1) order.distinct(3))
    done
next
  case (VSinceInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.split order.splits)
next
  case (VUntil x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.split order.splits)
    apply (metis order.distinct(1) order.distinct(3))
    done
next
  case (VUntilInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.split order.splits)
qed 

lemma trans_order_equal[simp]:
  "trans_order Eq b b"
  "trans_order b Eq b"
  by (intro trans_orderI, auto)+

declare trans_order_different[simp]

lemma invert_order_comparator_proof:
  assumes "ID ccompare = Some compa"
  shows "invert_order (comparator_sproof compa sp sp') = comparator_sproof compa sp' sp"
    "invert_order (comparator_vproof compa vp vp') = comparator_vproof compa vp' vp"
proof(induct sp and vp arbitrary: sp' and vp')
  case (STT x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SPred x1 x2 x3)
  then show ?case
    using assms
    apply (auto simp add: comparator_of_def ID_ccompare' comparator.sym comparator_list comparator_trm split: sproof.splits order.splits)
     apply (metis comparator_compare comparator_def compare_refl order.distinct(1))
    apply (metis comparator.sym comparator_compare invert_order.simps(2) order.distinct(5))
    done
next
  case (SNeg x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrL x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrR x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAnd x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (SImpL x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SImpR x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SIffSS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (SIffVV x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (SExists x1 x2 x3)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (verit) assms ccomp_comparator comparator.sym comparator_compare invert_order.simps(1-3) option.sel option.simps(3) order.simps(6))
    done
next
  case (SForall x1 x2)
  then show ?case sorry
next
  case (SPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SNext x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOnce x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SEventually x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SHistorically x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits order.splits)
next
  case (SHistoricallyOut x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAlways x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits order.splits)
next
  case (SSince x1 x2)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits if_splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (SUntil x1 x2)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits if_splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VFF x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPred x1 x2 x3)
  then show ?case 
    using assms
    apply (auto simp add: comparator_of_def ID_ccompare' comparator.sym comparator_list comparator_trm split: vproof.splits order.splits)
     apply (metis comparator_compare comparator_def compare_refl order.distinct(1))
    apply (metis comparator.sym comparator_compare invert_order.simps(2) order.distinct(5))
    done
next
  case (VNeg x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOr x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VAndL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAndR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VImp x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VIffSV x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VIffVS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VExists x1 x2)
  then show ?case sorry
next
  case (VForall x1 x2 x3)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (verit) assms ccomp_comparator comparator.sym comparator_compare invert_order.simps(1-3) option.sel option.simps(3) order.simps(6))
    done
next
  case (VPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case VPrevZ
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPrevOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPrevOutR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNext x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnce x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VEventually x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VHistorically x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAlways x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSinceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSince x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.splits order.splits if_splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VSinceInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VUntil x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.splits order.splits if_splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VUntilInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
qed

lemma trans_comparator_proof:
  assumes "ID ccompare = Some compa"
  shows "trans_order (comparator_sproof compa sp sp') (comparator_sproof compa sp' sp'') (comparator_sproof compa sp sp'')"
    "trans_order (comparator_vproof compa vp vp') (comparator_vproof compa vp' vp'') (comparator_vproof compa vp vp'')"
proof (induct sp and vp arbitrary: sp' sp'' and vp' vp'')
  case (STT x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SPred x1 x2 x3)
  then show ?case 
    using assms
    apply (auto simp add: comparator_of_def comparator.eq_Eq_conv ID_ccompare' assms comparator_list comparator_trm split: sproof.splits order.splits)
      apply (smt (verit, best) assms ccomp_comparator comparator.comp_trans comparator.weak_eq comparator_list comparator_trm invert_order.elims option.sel option.simps(3) trans_order_def)
     apply (metis comparator.sym comparator_compare invert_order.simps(1) order.distinct(5))
    apply (metis comparator.comp_trans comparator_compare order.distinct(5))
    done
next
  case (SNeg x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrL x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrR x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAnd x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (SImpL x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SImpR x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SIffSS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (SIffVV x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (SExists x1 x2 x3)
  then show ?case sorry
next
  case (SForall x1 x2)
  then show ?case sorry
next
  case (SPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SNext x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOnce x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SEventually x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SHistorically x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits order.splits)
next
  case (SHistoricallyOut x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAlways x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits order.splits)
next
  case (SSince x1 x2)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (verit) order.distinct(1,3) trans_order_def)
    done
next
  case (SUntil x1 x2)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (verit) order.distinct(1,3) trans_order_def)
    done
next
  case (VFF x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPred x1 x2 x3)
  then show ?case 
    using assms
    apply (auto simp add: comparator_of_def comparator.eq_Eq_conv ID_ccompare' assms comparator_list comparator_trm split: vproof.splits order.splits)
      apply (smt (verit, best) assms ccomp_comparator comparator.comp_trans comparator.weak_eq comparator_list comparator_trm invert_order.elims option.sel option.simps(3) trans_order_def)
     apply (metis comparator.sym comparator_compare invert_order.simps(1) order.distinct(5))
    apply (metis comparator.comp_trans comparator_compare order.distinct(5))
    done
next
  case (VNeg x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOr x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (VAndL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAndR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VImp x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (VIffSV x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (VIffVS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (VExists x1 x2)
  then show ?case sorry
next
  case (VForall x1 x2 x3)
  then show ?case sorry
next
  case (VPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case VPrevZ
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPrevOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPrevOutR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNext x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnce x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VEventually x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VHistorically x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAlways x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSinceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSince x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (verit) order.distinct(1,3) trans_order_def)
    done
next
  case (VSinceInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VUntil x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (verit) order.distinct(1,3) trans_order_def)
    done
next
  case (VUntilInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
qed


instance
   apply standard
   apply (force simp add: ccompare_sproof_def ccompare_vproof_def comparator_def
      eq_Eq_comparator_proof invert_order_comparator_proof intro: trans_comparator_proof[THEN trans_orderD(2)] split: option.splits)+
  done

end

instantiation part :: (type, type) equal begin

lift_definition equal_part :: "('a, 'b) part \<Rightarrow> ('a, 'b) part \<Rightarrow> bool" is "(=)" .

instance proof qed (simp add: equal_part_def Rep_part_inject)

end


derive (eq) ceq part
derive (eq) ceq sproof
derive (rbt) set_impl sproof
derive (eq) ceq vproof
derive (rbt) set_impl vproof

end