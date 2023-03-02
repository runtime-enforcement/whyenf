theory Monitor_Code
  imports Explanator2.Monitor "HOL-Library.Code_Target_Nat" Containers.Containers
    "HOL-Library.List_Lexorder"
begin

section \<open>Code\<close>

subsection \<open>Progress\<close>

primrec progress :: "'a trace \<Rightarrow> 'a MFOTL.formula \<Rightarrow> nat \<Rightarrow> nat" where
  "progress \<sigma> MFOTL.TT j = j"
| "progress \<sigma> MFOTL.FF j = j"
| "progress \<sigma> (MFOTL.Pred _ _) j = j"
| "progress \<sigma> (MFOTL.Neg \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (MFOTL.Or \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (MFOTL.And \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (MFOTL.Imp \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (MFOTL.Iff \<phi> \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (MFOTL.Exists _ \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (MFOTL.Forall _ \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (MFOTL.Prev I \<phi>) j = (if j = 0 then 0 else min (Suc (progress \<sigma> \<phi> j)) j)"
| "progress \<sigma> (MFOTL.Next I \<phi>) j = progress \<sigma> \<phi> j - 1"
| "progress \<sigma> (MFOTL.Once I \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (MFOTL.Historically I \<phi>) j = progress \<sigma> \<phi> j"
| "progress \<sigma> (MFOTL.Eventually I \<phi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I}"
| "progress \<sigma> (MFOTL.Always I \<phi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I}"
| "progress \<sigma> (MFOTL.Since \<phi> I \<psi>) j = min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j)"
| "progress \<sigma> (MFOTL.Until \<phi> I \<psi>) j =
    Inf {i. \<forall>k. k < j \<and> k \<le> min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) \<longrightarrow> (\<tau> \<sigma> k - \<tau> \<sigma> i) \<le> right I}"

lemma Inf_Min:
  fixes P :: "nat \<Rightarrow> bool"
  assumes "P j"
  shows "Inf (Collect P) = Min (Set.filter P {..j})"
  using Min_in[where ?A="Set.filter P {..j}"] assms
  by (auto simp: Set.filter_def intro: cInf_lower intro!: antisym[OF _ Min_le])
    (metis Inf_nat_def1 empty_iff mem_Collect_eq)

lemma progress_Eventually_code: "progress \<sigma> (MFOTL.Eventually I \<phi>) j =
  (let m = min j (Suc (progress \<sigma> \<phi> j)) - 1 in Min (Set.filter (\<lambda>i. enat (\<delta> \<sigma> m i) \<le> right I) {..j}))"
proof -
  define P where "P \<equiv> (\<lambda>i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> enat (\<delta> \<sigma> k i) \<le> right I)"
  have P_j: "P j"
    by (auto simp: P_def enat_0)
  have all_wit: "(\<forall>k \<in> {..<m}. enat (\<delta> \<sigma> k i) \<le> right I) \<longleftrightarrow> (enat (\<delta> \<sigma> (m - 1) i) \<le> right I)" for i m
  proof (cases m)
    case (Suc ma)
    have "k < Suc ma \<Longrightarrow> \<delta> \<sigma> k i \<le> \<delta> \<sigma> ma i" for k
      using \<tau>_mono
      unfolding less_Suc_eq_le
      by (rule diff_le_mono)
    then show ?thesis
      by (auto simp: Suc) (meson order.trans enat_ord_simps(1))
  qed (auto simp: enat_0)
  show ?thesis
    unfolding progress.simps Let_def P_def[symmetric] Inf_Min[where ?P=P, OF P_j] all_wit[symmetric]
    by (fastforce simp: P_def intro: arg_cong[where ?f=Min])
qed

lemma progress_Always_code: "progress \<sigma> (MFOTL.Always I \<phi>) j =
  (let m = min j (Suc (progress \<sigma> \<phi> j)) - 1 in Min (Set.filter (\<lambda>i. enat (\<delta> \<sigma> m i) \<le> right I) {..j}))"
proof -
  define P where "P \<equiv> (\<lambda>i. \<forall>k. k < j \<and> k \<le> (progress \<sigma> \<phi> j) \<longrightarrow> enat (\<delta> \<sigma> k i) \<le> right I)"
  have P_j: "P j"
    by (auto simp: P_def enat_0)
  have all_wit: "(\<forall>k \<in> {..<m}. enat (\<delta> \<sigma> k i) \<le> right I) \<longleftrightarrow> (enat (\<delta> \<sigma> (m - 1) i) \<le> right I)" for i m
  proof (cases m)
    case (Suc ma)
    have "k < Suc ma \<Longrightarrow> \<delta> \<sigma> k i \<le> \<delta> \<sigma> ma i" for k
      using \<tau>_mono
      unfolding less_Suc_eq_le
      by (rule diff_le_mono)
    then show ?thesis
      by (auto simp: Suc) (meson order.trans enat_ord_simps(1))
  qed (auto simp: enat_0)
  show ?thesis
    unfolding progress.simps Let_def P_def[symmetric] Inf_Min[where ?P=P, OF P_j] all_wit[symmetric]
    by (fastforce simp: P_def intro: arg_cong[where ?f=Min])
qed

lemma progress_Until_code: "progress \<sigma> (MFOTL.Until \<phi> I \<psi>) j =
  (let m = min j (Suc (min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j))) - 1 in Min (Set.filter (\<lambda>i. enat (\<delta> \<sigma> m i) \<le> right I) {..j}))"
proof -
  define P where "P \<equiv> (\<lambda>i. \<forall>k. k < j \<and> k \<le> min (progress \<sigma> \<phi> j) (progress \<sigma> \<psi> j) \<longrightarrow> enat (\<delta> \<sigma> k i) \<le> right I)"
  have P_j: "P j"
    by (auto simp: P_def enat_0)
  have all_wit: "(\<forall>k \<in> {..<m}. enat (\<delta> \<sigma> k i) \<le> right I) \<longleftrightarrow> (enat (\<delta> \<sigma> (m - 1) i) \<le> right I)" for i m
  proof (cases m)
    case (Suc ma)
    have "k < Suc ma \<Longrightarrow> \<delta> \<sigma> k i \<le> \<delta> \<sigma> ma i" for k
      using \<tau>_mono
      unfolding less_Suc_eq_le
      by (rule diff_le_mono)
    then show ?thesis
      by (auto simp: Suc) (meson order.trans enat_ord_simps(1))
  qed (auto simp: enat_0)
  show ?thesis
    unfolding progress.simps Let_def P_def[symmetric] Inf_Min[where ?P=P, OF P_j] all_wit[symmetric]
    by (fastforce simp: P_def intro: arg_cong[where ?f=Min])
qed

lemmas progress_code[code] = progress.simps(1-14) progress_Eventually_code progress_Always_code progress.simps(17) progress_Until_code

subsection \<open>Trace\<close>

lemma extend_is_stream: 
  assumes "sorted (map snd list)"
  and "\<And>x. x \<in> set list \<Longrightarrow> snd x \<le> m"
  shows "ssorted (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats)) \<and>
    sincreasing (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats))"
proof -
  have A: "\<forall>x\<in>set list. n \<le> snd x \<Longrightarrow> n \<le> m \<Longrightarrow>
    n \<le> (map snd list @- smap (\<lambda>x. x + m) nats) !! i" for n i 
    and list :: "('a set \<times> nat) list"
    apply (induction i arbitrary: n list)
     apply (auto simp add: list.map_sel(1))
    apply (metis (no_types, lifting) list.set_sel(2) map_tl)
    done
  have "ssorted (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats))"
    using assms
    apply (induction list)
     apply (auto simp: ssorted_iff_mono stream.map_comp o_def)
    subgoal for a b list i j
      using A
      by (cases i; cases j) fastforce+
    done
  moreover have "sincreasing (smap snd (list @- smap (\<lambda>n. ({}, n + m)) nats))"
    using assms
  proof (induction list)
    case Nil
    then show ?case
      by (simp add: sincreasing_def) presburger
  next
    case (Cons a as)
    have IH: "\<And>x. \<exists>i. x < smap snd (as @- smap (\<lambda>n. ({}, n + m)) nats) !! i"
      using Cons
      by (simp add: sincreasing_def)
    show ?case
      using IH
      by (simp add: sincreasing_def) 
        (metis snth_Stream)
  qed
  ultimately show ?thesis
    by simp
qed

typedef 'a trace_rbt = "{(n, m, t) :: (nat \<times> nat \<times> (nat, 'a set \<times> nat) mapping) |
  n m t. Mapping.keys t = {..<n} \<and>
  sorted (map (snd \<circ> (the \<circ> Mapping.lookup t)) [0..<n]) \<and>
  (case n of 0 \<Rightarrow> True | Suc n' \<Rightarrow> (case Mapping.lookup t n' of Some (X', t') \<Rightarrow> t' \<le> m | None \<Rightarrow> False))}"
  by (rule exI[of _ "(0, 0, Mapping.empty)"]) auto

setup_lifting type_definition_trace_rbt

lemma lookup_bulkload_Some: "i < length list \<Longrightarrow>
  Mapping.lookup (Mapping.bulkload list) i = Some (list ! i)"
  by transfer (auto simp: Map_To_Mapping.map_apply_def)

lift_definition trace_rbt_of_list :: "('a set \<times> nat) list \<Rightarrow> 'a trace_rbt" is
  "\<lambda>xs. if sorted (map snd xs) then (if xs = [] then (0, 0, Mapping.empty)
  else (length xs, snd (last xs), Mapping.bulkload xs))
  else (0, 0, Mapping.empty)"
  by (auto simp: lookup_bulkload_Some sorted_iff_nth_Suc last_conv_nth split: option.splits nat.splits)

lift_definition trace_rbt_nth :: "'a trace_rbt \<Rightarrow> nat \<Rightarrow> ('a set \<times> nat)" is
  "\<lambda>(n, m, t) i. if i < n then the (Mapping.lookup t i) else ({}, (i - n) + m)" .

lift_definition Trace_RBT :: "'a trace_rbt \<Rightarrow> 'a trace" is
  "\<lambda>(n, m, t). map (the \<circ> Mapping.lookup t) [0..<n] @- smap (\<lambda>n. ({} :: 'a set, n + m)) nats"
  subgoal premises prems for prod
  proof -
    obtain n m t where prod_def: "prod = (n, m, t)"
      by (cases prod) auto
    have props: "Mapping.keys t = {..<n}"
      "sorted (map (snd \<circ> (the \<circ> Mapping.lookup t)) [0..<n])"
      "(case n of 0 \<Rightarrow> True | Suc n' \<Rightarrow> (case Mapping.lookup t n' of Some (X', t') \<Rightarrow> t' \<le> m | None \<Rightarrow> False))"
      using prems
      by (auto simp: prod_def)
    have aux: "x \<in> set (map (the \<circ> Mapping.lookup t) [0..<n]) \<Longrightarrow> snd x \<le> m" for x
      using props(2,3) less_Suc_eq_le
      by (fastforce simp: sorted_iff_nth_mono split: nat.splits option.splits)
    show ?thesis
      apply (simp add: prod_def del: smap_shift)
      apply (rule extend_is_stream[where ?m=m])
      using props aux
      by (auto simp: prod_def)
  qed
  done

code_datatype Trace_RBT

definition "trace_of_list xs = Trace_RBT (trace_rbt_of_list xs)"

lemma \<Gamma>_rbt_code[code]: "\<Gamma> (Trace_RBT t) i = fst (trace_rbt_nth t i)"
  by transfer (auto split: prod.splits)

lemma \<tau>_rbt_code[code]: "\<tau> (Trace_RBT t) i = snd (trace_rbt_nth t i)"
  by transfer (auto split: prod.splits)
                                       
lemma trace_rbt_of_list_sound: "sorted (map snd xs) \<Longrightarrow> i < length xs \<Longrightarrow>
  xs ! i = (\<Gamma> (trace_of_list xs) i, \<tau> (trace_of_list xs) i)"
  unfolding trace_of_list_def
  by transfer (auto simp: lookup_bulkload_Some)

subsection \<open>Exported functions\<close>

definition str_s_check :: "String.literal MFOTL.trace \<Rightarrow> (char list \<Rightarrow> String.literal set) \<Rightarrow> _ MFOTL.formula \<Rightarrow> _ sproof \<Rightarrow> bool"
  where "str_s_check = s_check_exec"

definition str_s_at :: "String.literal sproof \<Rightarrow> nat"
  where "str_s_at = s_at"

definition str_v_check :: "String.literal MFOTL.trace \<Rightarrow> (char list \<Rightarrow> String.literal set) \<Rightarrow> _ MFOTL.formula \<Rightarrow> _ vproof \<Rightarrow> bool"
  where "str_v_check = v_check_exec"

definition str_v_at :: "String.literal vproof \<Rightarrow> nat"
  where "str_v_at = v_at"

definition is_valid :: "String.literal MFOTL.trace \<Rightarrow> (char list \<Rightarrow> String.literal set) \<Rightarrow> _ MFOTL.formula \<Rightarrow> (_ proof) \<Rightarrow> bool"
  where "is_valid = p_check_exec"

declare MFOTL.future_bounded.simps[code]

(* context 
  fixes \<sigma> :: "'d :: linorder MFOTL.trace" and
  cmp :: "'d proof \<Rightarrow> 'd proof \<Rightarrow> bool"
begin

lemma opt_code[code]: "optimal vs i \<phi> p = (if MFOTL.future_bounded \<phi> then
  valid \<sigma> i \<phi> p \<and> cmp p (opt vars i \<phi>) else Code.abort (STR ''opt: formula is not future bounded'') (\<lambda>_. optimal i \<phi> p))"
  using alg_optimal[of \<phi> i] trans_cmp
  by (auto simp: optimal_def transp_def)

end *)

subsection \<open>Auxiliary results\<close>

definition "sum_proofs f xs = sum_list (map f xs)"

lemma sum_proofs_empty[simp]: "sum_proofs f [] = 0"
  by (auto simp: sum_proofs_def)

lemma sum_proofs_fundef_cong[fundef_cong]: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = f' x) \<Longrightarrow>
  sum_proofs f xs = sum_proofs f' xs"
  by (induction xs) (auto simp: sum_proofs_def)

lemma sum_proofs_Cons:
  fixes f :: "'a \<Rightarrow> nat"
  shows "sum_proofs f (p # qs) = f p + sum_proofs f qs"
  by (auto simp: sum_proofs_def split: list.splits)

lemma sum_proofs_app:
  fixes f :: "'a \<Rightarrow> nat"
  shows "sum_proofs f (qs @ [p]) = f p + sum_proofs f qs"
  by (auto simp: sum_proofs_def split: list.splits)

context
  fixes w :: "string \<Rightarrow> nat"
begin

function (sequential) s_pred :: "'d sproof \<Rightarrow> nat" 
  and v_pred :: "'d vproof \<Rightarrow> nat" where
  "s_pred (STT _) = 1"
| "s_pred (SPred _ r _) = w r"
| "s_pred (SNeg vp) = (v_pred vp) + 1"
| "s_pred (SOrL sp1) = (s_pred sp1) + 1"
| "s_pred (SOrR sp2) = (s_pred sp2) + 1"
| "s_pred (SAnd sp1 sp2) = (s_pred sp1) + (s_pred sp2) + 1"
| "s_pred (SImpL vp1) = (v_pred vp1) + 1"
| "s_pred (SImpR sp2) = (s_pred sp2) + 1"
| "s_pred (SIffSS sp1 sp2) = (s_pred sp1) + (s_pred sp2) + 1"
| "s_pred (SIffVV vp1 vp2) = (v_pred vp1) + (v_pred vp2) + 1"
| "s_pred (SExists _ _ sp) = (s_pred sp) + 1"
| "s_pred (SForall _ part) = (sum_proofs s_pred (vals part)) + 1"
| "s_pred (SPrev sp) = (s_pred sp) + 1"
| "s_pred (SNext sp) = (s_pred sp) + 1"
| "s_pred (SOnce _ sp) = (s_pred sp) + 1"
| "s_pred (SEventually _ sp) = (s_pred sp) + 1"
| "s_pred (SHistorically _ _ sps) = (sum_proofs s_pred sps) + 1"
| "s_pred (SHistoricallyOut _) = 1"
| "s_pred (SAlways _ _ sps) = (sum_proofs s_pred sps) + 1"
| "s_pred (SSince sp2 sp1s) = (sum_proofs s_pred (sp2 # sp1s)) + 1"
| "s_pred (SUntil sp1s sp2) = (sum_proofs s_pred (sp1s @ [sp2])) + 1"
| "v_pred (VFF _ ) = 1"
| "v_pred (VPred _ r _) = w r"
| "v_pred (VNeg sp) = (s_pred sp) + 1"
| "v_pred (VOr vp1 vp2) = ((v_pred vp1) + (v_pred vp2)) + 1"
| "v_pred (VAndL vp1) = (v_pred vp1) + 1"
| "v_pred (VAndR vp2) = (v_pred vp2) + 1"
| "v_pred (VImp sp1 vp2) = ((s_pred sp1) + (v_pred vp2)) + 1"
| "v_pred (VIffSV sp1 vp2) = ((s_pred sp1) + (v_pred vp2)) + 1"
| "v_pred (VIffVS vp1 sp2) = ((v_pred vp1) + (s_pred sp2)) + 1"
| "v_pred (VExists _ part) = (sum_proofs v_pred (vals part)) + 1"
| "v_pred (VForall _ _ vp) = (v_pred vp) + 1"
| "v_pred (VPrev vp) = (v_pred vp) + 1"
| "v_pred (VPrevZ) = 1"
| "v_pred (VPrevOutL _) = 1"
| "v_pred (VPrevOutR _) = 1"
| "v_pred (VNext vp) = (v_pred vp) + 1"
| "v_pred (VNextOutL _) = 1"
| "v_pred (VNextOutR _) = 1"
| "v_pred (VOnceOut _) = 1"
| "v_pred (VOnce _ _ vps) = (sum_proofs v_pred vps) + 1"
| "v_pred (VEventually _ _ vps) = (sum_proofs v_pred vps) + 1"
| "v_pred (VHistorically _ vp) = (v_pred vp) + 1"
| "v_pred (VAlways _ vp) = (v_pred vp) + 1"
| "v_pred (VSinceOut _) = 1"
| "v_pred (VSince _ vp1 vp2s) = (sum_proofs v_pred (vp1 # vp2s)) + 1"
| "v_pred (VSinceInf _ _ vp2s) = (sum_proofs v_pred vp2s) + 1"
| "v_pred (VUntil _ vp2s vp1) = (sum_proofs v_pred (vp2s @ [vp1])) + 1"
| "v_pred (VUntilInf _ _ vp2s) = (sum_proofs v_pred vp2s) + 1"
  by pat_completeness auto
termination
  by (relation "measure (case_sum size size)")
    (auto simp add: termination_simp)

definition p_pred :: "'d proof \<Rightarrow> nat" where
  "p_pred = case_sum s_pred v_pred"

end

subsection \<open>\<^const>\<open>v_check_exec\<close> setup\<close>

lemma ETP_minus_le_iff: "ETP \<sigma> (\<tau> \<sigma> i - n) \<le> j \<longleftrightarrow> \<delta> \<sigma> i j \<le> n"
  by (simp add: add.commute i_ETP_tau le_diff_conv)

lemma ETP_minus_gt_iff: "j < ETP \<sigma> (\<tau> \<sigma> i - n) \<longleftrightarrow> \<delta> \<sigma> i j > n"
  by (meson ETP_minus_le_iff leD le_less_linear)

lemma nat_le_iff_less:
  fixes n :: nat
  shows "(j \<le> n) \<longleftrightarrow> (j = 0 \<or> j - 1 < n)"
  by auto

lemma ETP_minus_eq_iff: "j = ETP \<sigma> (\<tau> \<sigma> i - n) \<longleftrightarrow> ((j = 0 \<or> n < \<delta> \<sigma> i (j - 1)) \<and> \<delta> \<sigma> i j \<le> n)"
  unfolding eq_iff[of j "ETP \<sigma> (\<tau> \<sigma> i - n)"] nat_le_iff_less[of j] ETP_minus_le_iff ETP_minus_gt_iff
  by auto

lemma LTP_minus_ge_iff: "\<tau> \<sigma> 0 + n \<le> \<tau> \<sigma> i \<Longrightarrow> j \<le> LTP \<sigma> (\<tau> \<sigma> i - n) \<longleftrightarrow>
  (case n of 0 \<Rightarrow> \<delta> \<sigma> j i = 0 | _ \<Rightarrow> j \<le> i \<and> \<delta> \<sigma> i j \<ge> n)"
  by (auto simp add: i_LTP_tau split: nat.splits)
     (smt (z3) add.commute add_Suc_right add_leD2 ETP_ge i_ETP_tau le_diff_conv2 less_le_trans less_or_eq_imp_le plus_1_eq_Suc)

lemma LTP_plus_ge_iff: "j \<le> LTP \<sigma> (\<tau> \<sigma> i + n) \<longleftrightarrow> \<delta> \<sigma> j i \<le> n"
  by (smt (z3) \<tau>_mono diff_self_eq_0 i_LTP_tau le_diff_conv le_imp_diff_is_add nat_le_iff_add trans_le_add2 add.commute)

lemma LTP_minus_lt_if:
  assumes "j \<le> i" "\<tau> \<sigma> 0 + n \<le> \<tau> \<sigma> i" "\<delta> \<sigma> i j < n"
  shows "LTP \<sigma> (\<tau> \<sigma> i - n) < j"
proof -
  have not_in: "k \<notin> {ia. \<tau> \<sigma> ia \<le> \<tau> \<sigma> i - n}" if "j \<le> k" for k
    using assms \<tau>_mono[OF that, of \<sigma>]
    by auto
  then have "{ia. \<tau> \<sigma> ia \<le> \<tau> \<sigma> i - n} \<subseteq> {0..<j}"
    using not_le_imp_less
    by (clarsimp; blast)
  then have "finite {ia. \<tau> \<sigma> ia \<le> \<tau> \<sigma> i - n}"
    using subset_eq_atLeast0_lessThan_finite
    by blast
  moreover have "0 \<in> {ia. \<tau> \<sigma> ia \<le> \<tau> \<sigma> i - n}"
    using assms(2)
    by auto
  ultimately show ?thesis
    unfolding LTP_def
    by (metis Max_in not_in empty_iff not_le_imp_less)
qed

lemma diff_cancel_middle: "(c::nat) \<le> b + a \<Longrightarrow> a - (b + a - c) = c - b"
  by simp

lemma LTP_minus_lt_iff:
  assumes "\<tau> \<sigma> 0 + n \<le> \<tau> \<sigma> i"
  shows "LTP \<sigma> (\<tau> \<sigma> i - n) < j \<longleftrightarrow> (if \<not> j \<le> i \<and> n = 0 then \<delta> \<sigma> j i > 0 else \<delta> \<sigma> i j < n)"
proof (cases "j \<le> i")
  case True
  then show ?thesis
    using assms i_le_LTPi_minus[of \<sigma> n i] LTP_minus_lt_if[of j i \<sigma> n]
    apply (cases n)
    apply (simp add: i_LTP_tau linorder_not_less)
    apply (smt (verit) diff_cancel_middle \<tau>_mono diff_is_0_eq diff_le_self i_LTP_tau le_add_diff_inverse2 le_trans not_le_imp_less zero_less_diff)
    done
next
  case False
  have delta: "\<delta> \<sigma> i j = 0"
    using False
    by auto
  show ?thesis
  proof (cases n)
    case 0
    then show ?thesis
      using False assms
      by (simp add: i_LTP_tau not_le_imp_less)
        (metis "0" Nat.add_0_right assms i_LTP_tau linorder_not_less)
  next
    case (Suc n')
    then show ?thesis
      using False assms
      by simp (metis (no_types, lifting) Zero_not_Suc add_Suc_right add_diff_cancel_left' diff_is_0_eq' i_le_LTPi_minus le_less_trans less_or_eq_imp_le neq0_conv not_le_imp_less)
  qed
qed

lemma LTP_minus_eq_iff:
  assumes "\<tau> \<sigma> 0 + n \<le> \<tau> \<sigma> i"
  shows "j = LTP \<sigma> (\<tau> \<sigma> i - n) \<longleftrightarrow>
  (case n of 0 \<Rightarrow> i \<le> j \<and> \<delta> \<sigma> j i = 0 \<and> \<delta> \<sigma> (Suc j) j > 0
  | _ \<Rightarrow> j \<le> i \<and> n \<le> \<delta> \<sigma> i j \<and> \<delta> \<sigma> i (Suc j) < n)"
proof (cases n)
  case 0
  show ?thesis
    using assms
    apply (auto simp: 0 i_le_LTPi)
      apply (metis "0" add_0_right assms i_LTP_tau order_refl)
     apply (metis add.right_neutral Suc_n_not_le_n \<tau>_mono eq_imp_le i_LTP_tau le_add2 le_neq_implies_less plus_1_eq_Suc)
    apply (metis "0" add.right_neutral assms i_LTP_tau leD le_\<tau>_less le_less_Suc_eq le_less_linear le_neq_implies_less)
    done
next
  case (Suc n')
  show ?thesis
    using assms
    by (simp add: Suc eq_iff[of j "LTP \<sigma> (\<tau> \<sigma> i - Suc n')"] less_Suc_eq_le[of "LTP \<sigma> (\<tau> \<sigma> i - Suc n')" j, symmetric] LTP_minus_ge_iff LTP_minus_lt_iff)
qed

lemma LTP_plus_eq_iff:
  shows "j = LTP \<sigma> (\<tau> \<sigma> i + n) \<longleftrightarrow> (\<delta> \<sigma> j i \<le> n \<and> \<delta> \<sigma> (Suc j) i > n)"
  unfolding eq_iff[of j "LTP \<sigma> (\<tau> \<sigma> i + n)"]
  by (meson LTP_plus_ge_iff linorder_not_less not_less_eq_eq)

lemma LTP_p_def: "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i \<Longrightarrow> LTP_p \<sigma> i I = (case left I of 0 \<Rightarrow> i | _ \<Rightarrow> LTP \<sigma> (\<tau> \<sigma> i - left I))"
  using i_le_LTPi
  by (simp add: min_def split: nat.splits)
    (smt (verit, ccfv_threshold) Zero_not_Suc add_leD2 add_le_imp_le_diff diff_diff_cancel diff_is_0_eq' i_LTP_tau i_le_LTPi)

definition "check_upt_LTP_p \<sigma> I li xs i \<longleftrightarrow> (case xs of [] \<Rightarrow>
  (case left I of 0 \<Rightarrow> i < li | Suc n \<Rightarrow>
    (if \<not> li \<le> i \<and> left I = 0 then 0 < \<delta> \<sigma> li i else \<delta> \<sigma> i li < left I))
  | _ \<Rightarrow> xs = [li..<li + length xs] \<and>
    (case left I of 0 \<Rightarrow> li + length xs - 1 = i | Suc n \<Rightarrow>
      (li + length xs - 1 \<le> i \<and> left I \<le> \<delta> \<sigma> i (li + length xs - 1) \<and> \<delta> \<sigma> i (li + length xs) < left I)))"

lemma check_upt_l_cong:
  assumes "\<And>j. j \<le> max i li \<Longrightarrow> \<tau> \<sigma> j = \<tau> \<sigma>' j"
  shows "check_upt_LTP_p \<sigma> I li xs i = check_upt_LTP_p \<sigma>' I li xs i"
proof -
  have "li + length ys \<le> i \<Longrightarrow> Suc n \<le> \<delta> \<sigma>' i (li + length ys) \<Longrightarrow>
    (Suc (li + length ys)) \<le> i" for ys :: "nat list" and n
    by (cases "li + length ys = i") auto
  then show ?thesis
    using assms
    by (fastforce simp: check_upt_LTP_p_def Let_def simp del: upt.simps split: list.splits nat.splits)
qed

lemma check_upt_LTP_p_eq:
  assumes "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
  shows "xs = [li..<Suc (LTP_p \<sigma> i I)] \<longleftrightarrow> check_upt_LTP_p \<sigma> I li xs i"
proof -
  have "li + length xs = Suc (LTP_p \<sigma> i I) \<longleftrightarrow> li + length xs - 1 = LTP_p \<sigma> i I" if "xs \<noteq> []"
    using that
    by (cases xs) auto
  then have "xs = [li..<Suc (LTP_p \<sigma> i I)] \<longleftrightarrow> (xs = [] \<and> LTP_p \<sigma> i I < li) \<or>
    (xs \<noteq> [] \<and> xs = [li..<li + length xs] \<and> li + length xs - 1 = LTP_p \<sigma> i I)"
    by auto
  moreover have "\<dots> \<longleftrightarrow> (xs = [] \<and>
    (case left I of 0 \<Rightarrow> i < li | Suc n \<Rightarrow>
      (if \<not> li \<le> i \<and> left I = 0 then 0 < \<delta> \<sigma> li i else \<delta> \<sigma> i li < left I))) \<or>
    (xs \<noteq> [] \<and> xs = [li..<li + length xs] \<and>
    (case left I of 0 \<Rightarrow> li + length xs - 1 = i | Suc n \<Rightarrow>
      (case left I of 0 \<Rightarrow> i \<le> li + length xs - 1 \<and>
        \<delta> \<sigma> (li + length xs - 1) i = 0 \<and> 0 < \<delta> \<sigma> (Suc (li + length xs - 1)) (li + length xs - 1)
      | Suc n \<Rightarrow> li + length xs - 1 \<le> i \<and>
        left I \<le> \<delta> \<sigma> i (li + length xs - 1) \<and> \<delta> \<sigma> i (Suc (li + length xs - 1)) < left I)))"
    using LTP_p_def[OF assms, symmetric]
    unfolding LTP_minus_lt_iff[OF assms, symmetric]
    unfolding LTP_minus_eq_iff[OF assms, symmetric]
    by (auto split: nat.splits)
  moreover have "\<dots> \<longleftrightarrow> (case xs of [] \<Rightarrow>
    (case left I of 0 \<Rightarrow> i < li | Suc n \<Rightarrow>
      (if \<not> li \<le> i \<and> left I = 0 then 0 < \<delta> \<sigma> li i else \<delta> \<sigma> i li < left I))
    | _ \<Rightarrow> xs = [li..<li + length xs] \<and>
      (case left I of 0 \<Rightarrow> li + length xs - 1 = i | Suc n \<Rightarrow>
        (li + length xs - 1 \<le> i \<and> left I \<le> \<delta> \<sigma> i (li + length xs - 1) \<and> \<delta> \<sigma> i (li + length xs) < left I)))"
    by (auto split: nat.splits list.splits)
  ultimately show ?thesis
    unfolding check_upt_LTP_p_def
    by simp
qed

lemma v_check_exec_Once_code[code]: "v_check_exec \<sigma> vs (MFOTL.Once I \<phi>) vp = (case vp of
  VOnce i li vps \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> li = 0 | enat b \<Rightarrow> ((li = 0 \<or> b < \<delta> \<sigma> i (li - 1)) \<and> \<delta> \<sigma> i li \<le> b)) 
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> check_upt_LTP_p \<sigma> I li (map v_at vps) i \<and> Ball (set vps) (v_check_exec \<sigma> vs \<phi>)
  | VOnceOut i \<Rightarrow> \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I 
  | _ \<Rightarrow> False)"
  by (auto simp: Let_def check_upt_LTP_p_eq ETP_minus_le_iff ETP_minus_eq_iff split: vproof.splits enat.splits simp del: upt_Suc)

lemma s_check_exec_Historically_code[code]: "s_check_exec \<sigma> vs (MFOTL.Historically I \<phi>) vp = (case vp of
  SHistorically i li vps \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> li = 0 | enat b \<Rightarrow> ((li = 0 \<or> b < \<delta> \<sigma> i (li - 1)) \<and> \<delta> \<sigma> i li \<le> b))
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> check_upt_LTP_p \<sigma> I li (map s_at vps) i \<and> Ball (set vps) (s_check_exec \<sigma> vs \<phi>)
  | SHistoricallyOut i \<Rightarrow> \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I 
  | _ \<Rightarrow> False)"
  by (auto simp: Let_def check_upt_LTP_p_eq ETP_minus_le_iff ETP_minus_eq_iff split: sproof.splits enat.splits simp del: upt_Suc)

lemma v_check_exec_Since_code[code]: "v_check_exec \<sigma> vs (MFOTL.Since \<phi> I \<psi>) vp = (case vp of
  VSince i vp1 vp2s \<Rightarrow>
    let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> \<delta> \<sigma> i j \<le> b) \<and> j \<le> i
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> check_upt_LTP_p \<sigma> I j (map v_at vp2s) i
    \<and> v_check_exec \<sigma> vs \<phi> vp1 \<and> Ball (set vp2s) (v_check_exec \<sigma> vs \<psi>)
  | VSinceInf i li vp2s \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> li = 0 | enat b \<Rightarrow> ((li = 0 \<or> b < \<delta> \<sigma> i (li - 1)) \<and> \<delta> \<sigma> i li \<le> b)) \<and>
    \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i \<and>
     check_upt_LTP_p \<sigma> I li (map v_at vp2s) i \<and> Ball (set vp2s) (v_check_exec \<sigma> vs \<psi>)
  | VSinceOut i \<Rightarrow> \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I 
  | _ \<Rightarrow> False)"
  by (auto simp: Let_def check_upt_LTP_p_eq ETP_minus_le_iff ETP_minus_eq_iff split: vproof.splits enat.splits simp del: upt_Suc)

lemma ETP_f_le_iff: "max i (ETP \<sigma> (\<tau> \<sigma> i + a)) \<le> j \<longleftrightarrow> i \<le> j \<and> \<delta> \<sigma> j i \<ge> a"
  by (metis add.commute max.bounded_iff \<tau>_mono i_ETP_tau le_diff_conv2)

lemma ETP_f_ge_iff: "j \<le> max i (ETP \<sigma> (\<tau> \<sigma> i + n)) \<longleftrightarrow> (case n of 0 \<Rightarrow> j \<le> i
  | Suc n' \<Rightarrow> (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<delta> \<sigma> j' i < n))"
proof (cases n)
  case 0
  then show ?thesis
    by (auto simp: max_def) (metis i_ge_etpi verit_la_disequality)
next
  case (Suc n')
  have max: "max i (ETP \<sigma> (\<tau> \<sigma> i + n)) = ETP \<sigma> (\<tau> \<sigma> i + n)"
    by (auto simp: max_def Suc)
       (metis Groups.ab_semigroup_add_class.add.commute ETP_ge less_or_eq_imp_le plus_1_eq_Suc)
  have "j \<le> max i (ETP \<sigma> (\<tau> \<sigma> i + n)) \<longleftrightarrow> (\<forall>ia. \<tau> \<sigma> i + n \<le> \<tau> \<sigma> ia \<longrightarrow> j \<le> ia)"
    unfolding max
    unfolding ETP_def
    by (meson LeastI_ex Least_le order.trans ex_le_\<tau>)
  moreover have "\<dots> \<longleftrightarrow> (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<not>\<tau> \<sigma> i + n \<le> \<tau> \<sigma> j')"
    by (auto split: nat.splits) (meson i_ETP_tau le_trans not_less_eq_eq)
  moreover have "\<dots> \<longleftrightarrow> (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<delta> \<sigma> j' i < n)"
    by (auto simp: Suc split: nat.splits)
  ultimately show ?thesis
    by (auto simp: Suc)
qed

definition "check_upt_ETP_f \<sigma> I i xs hi \<longleftrightarrow> (let j = Suc hi - length xs in
  (case xs of [] \<Rightarrow> (case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> \<delta> \<sigma> hi i < left I)
  | _ \<Rightarrow> (xs = [j..<Suc hi] \<and>
  (case left I of 0 \<Rightarrow> j \<le> i | Suc n' \<Rightarrow>
  (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<delta> \<sigma> j' i < left I)) \<and>
  i \<le> j \<and> left I \<le> \<delta> \<sigma> j i)))"

lemma check_upt_lu_cong:
  assumes "\<And>j. min i hi \<le> j \<and> j \<le> max i hi \<Longrightarrow> \<tau> \<sigma> j = \<tau> \<sigma>' j"
  shows "check_upt_ETP_f \<sigma> I i xs hi = check_upt_ETP_f \<sigma>' I i xs hi"
  using assms
  unfolding check_upt_ETP_f_def
  apply (auto simp add: Let_def del: upt.simps split: list.splits nat.splits)
   apply (metis Suc_leD diff_is_0_eq' diff_le_self le_Suc_eq not_less_zero order_less_le_trans)
  apply (metis add_leD2 cancel_comm_monoid_add_class.diff_cancel diff_le_self leD le_Suc_eq plus_1_eq_Suc zero_less_Suc)
  done

lemma check_upt_ETP_f_eq: "xs = [ETP_f \<sigma> i I..<Suc hi] \<longleftrightarrow> check_upt_ETP_f \<sigma> I i xs hi"
proof -
  have F1: "(case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> \<delta> \<sigma> hi i < left I) =
    (Suc hi \<le> ETP_f \<sigma> i I)"
    unfolding ETP_f_ge_iff[where ?j="Suc hi" and ?n="left I"]
    by (auto split: nat.splits)
  have "xs = [ETP_f \<sigma> i I..<Suc hi] \<longleftrightarrow> (let j = Suc hi - length xs in
    (xs = [] \<and> (case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> \<delta> \<sigma> hi i < left I)) \<or>
    (xs \<noteq> [] \<and> xs = [j..<Suc hi] \<and>
    (case left I of 0 \<Rightarrow> j \<le> i | Suc n' \<Rightarrow>
    (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<delta> \<sigma> j' i < left I)) \<and>
    i \<le> j \<and> left I \<le> \<delta> \<sigma> j i))"
    unfolding F1
    unfolding Let_def
    unfolding ETP_f_ge_iff[where ?n="left I", symmetric]
    unfolding ETP_f_le_iff[symmetric]
    unfolding eq_iff[of _ "ETP_f \<sigma> i I", symmetric]
    by auto
  moreover have "\<dots> \<longleftrightarrow> (let j = Suc hi - length xs in
    (case xs of [] \<Rightarrow> (case left I of 0 \<Rightarrow> Suc hi \<le> i | Suc n' \<Rightarrow> \<delta> \<sigma> hi i < left I)
    | _ \<Rightarrow> (xs = [j..<Suc hi] \<and>
    (case left I of 0 \<Rightarrow> j \<le> i | Suc n' \<Rightarrow>
    (case j of 0 \<Rightarrow> True | Suc j' \<Rightarrow> \<delta> \<sigma> j' i < left I)) \<and>
    i \<le> j \<and> left I \<le> \<delta> \<sigma> j i)))"
    by (auto simp: Let_def split: list.splits)
  finally show ?thesis
    unfolding check_upt_ETP_f_def .
qed

lemma v_check_exec_Eventually_code[code]: "v_check_exec \<sigma> vs (MFOTL.Eventually I \<phi>) vp = (case vp of
  VEventually i hi vps \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> False | enat b \<Rightarrow> (\<delta> \<sigma> hi i \<le> b \<and> b < \<delta> \<sigma> (Suc hi) i)) \<and>
     check_upt_ETP_f \<sigma> I i (map v_at vps) hi \<and> Ball (set vps) (v_check_exec \<sigma> vs \<phi>)
  | _ \<Rightarrow> False)"
  by (auto simp: Let_def LTP_plus_ge_iff LTP_plus_eq_iff check_upt_ETP_f_eq simp del: upt_Suc
      split: vproof.splits enat.splits)

lemma s_check_exec_Always_code[code]: "s_check_exec \<sigma> vs (MFOTL.Always I \<phi>) sp = (case sp of
  SAlways i hi sps \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> False | enat b \<Rightarrow> (\<delta> \<sigma> hi i \<le> b \<and> b < \<delta> \<sigma> (Suc hi) i)) 
    \<and> check_upt_ETP_f \<sigma> I i (map s_at sps) hi \<and> Ball (set sps) (s_check_exec \<sigma> vs \<phi>)
  | _ \<Rightarrow> False)"
  by (auto simp: Let_def LTP_plus_ge_iff LTP_plus_eq_iff check_upt_ETP_f_eq simp del: upt_Suc
      split: sproof.splits enat.splits)

lemma v_check_exec_Until_code[code]: "v_check_exec \<sigma> vs (MFOTL.Until \<phi> I \<psi>) vp = (case vp of
  VUntil i vp2s vp1 \<Rightarrow>
    let j = v_at vp1 in 
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> \<delta> \<sigma> j i \<le> b)
    \<and> i \<le> j \<and> check_upt_ETP_f \<sigma> I i (map v_at vp2s) j
    \<and> v_check_exec \<sigma> vs \<phi> vp1 \<and> Ball (set vp2s) (v_check_exec \<sigma> vs \<psi>)
 | VUntilInf i hi vp2s \<Rightarrow>
    (case right I of \<infinity> \<Rightarrow> False | enat b \<Rightarrow> (\<delta> \<sigma> hi i \<le> b \<and> b < \<delta> \<sigma> (Suc hi) i)) \<and>
     check_upt_ETP_f \<sigma> I i (map v_at vp2s) hi \<and> Ball (set vp2s) (v_check_exec \<sigma> vs \<psi>)
 | _ \<Rightarrow> False)"
  by (auto simp: Let_def LTP_plus_ge_iff LTP_plus_eq_iff check_upt_ETP_f_eq simp del: upt_Suc
      split: vproof.splits enat.splits)

subsection\<open>ETP/LTP setup\<close>

lemma ETP_aux: "\<not> t \<le> \<tau> \<sigma> i \<Longrightarrow> i \<le> (LEAST i. t \<le> \<tau> \<sigma> i)"
  by (meson LeastI_ex \<tau>_mono ex_le_\<tau> nat_le_linear order_trans)

function ETP_rec where
  "ETP_rec \<sigma> t i = (if \<tau> \<sigma> i \<ge> t then i else ETP_rec \<sigma> t (i + 1))"
  by pat_completeness auto
termination
  using ETP_aux
  by (relation "measure (\<lambda>(\<sigma>, t, i). Suc (ETP \<sigma> t) - i)")
    (fastforce simp: ETP_def)+

lemma ETP_rec_sound: "ETP_rec \<sigma> t j = (LEAST i. i \<ge> j \<and> t \<le> \<tau> \<sigma> i)"
proof (induction \<sigma> t j rule: ETP_rec.induct)
  case (1 \<sigma> t i)
  show ?case
  proof (cases "\<tau> \<sigma> i \<ge> t")
    case True
    then show ?thesis
      by simp (metis (no_types, lifting) Least_equality order_refl)
  next
    case False
    then show ?thesis
      using 1[OF False]
      by (simp add: ETP_rec.simps[of _ _ i] del: ETP_rec.simps)
         (metis Suc_leD le_antisym not_less_eq_eq)
  qed
qed

lemma ETP_code[code]: "ETP \<sigma> t = ETP_rec \<sigma> t 0"
  using ETP_rec_sound[of \<sigma> t 0]
  by (auto simp: ETP_def)

lemma LTP_aux:
  assumes "\<tau> \<sigma> (Suc i) \<le> t"
  shows "i \<le> Max {i. \<tau> \<sigma> i \<le> t}"
proof -
  have "finite {i. \<tau> \<sigma> i \<le> t}"
    by (smt (verit, del_insts) \<tau>_mono finite_nat_set_iff_bounded_le i_LTP_tau le0 le_trans mem_Collect_eq) 
  moreover have "i \<in> {i. \<tau> \<sigma> i \<le> t}"
    using le_trans[OF \<tau>_mono[of i "Suc i" \<sigma>] assms]
    by auto
  ultimately show ?thesis
    by (rule Max_ge)
qed

function LTP_rec where
  "LTP_rec \<sigma> t i = (if \<tau> \<sigma> (Suc i) \<le> t then LTP_rec \<sigma> t (i + 1) else i)"
  by pat_completeness auto
termination
  using LTP_aux
  by (relation "measure (\<lambda>(\<sigma>, t, i). Suc (LTP \<sigma> t) - i)") (fastforce simp: LTP_def)+

lemma max_aux: "finite X \<Longrightarrow> Suc j \<in> X \<Longrightarrow> Max (insert (Suc j) (X - {j})) = Max (insert j X)"
  (* sledgehammer *)
  by (smt (verit) max.orderI Max.insert_remove Max_ge Max_insert empty_iff insert_Diff_single
      insert_absorb insert_iff max_def not_less_eq_eq)

lemma LTP_rec_sound: "LTP_rec \<sigma> t j = Max ({i. i \<ge> j \<and> (\<tau> \<sigma> i) \<le> t} \<union> {j})"
proof (induction \<sigma> t j rule: LTP_rec.induct)
  case (1 \<sigma> t j)
  have fin: "finite {i. j \<le> i \<and> \<tau> \<sigma> i \<le> t}"
    by (smt (verit, del_insts) \<tau>_mono finite_nat_set_iff_bounded_le i_LTP_tau le0 le_trans
        mem_Collect_eq)
  show ?case
  proof (cases "\<tau> \<sigma> (Suc j) \<le> t")
    case True
    have diffI: "{i. Suc j \<le> i \<and> \<tau> \<sigma> i \<le> t} = {i. j \<le> i \<and> \<tau> \<sigma> i \<le> t} - {j}"
      by auto
    show ?thesis
      using 1[OF True] True fin
      by (auto simp del: LTP_rec.simps simp add: LTP_rec.simps[of _ _ j] diffI intro: max_aux)
  next
    case False
    then show ?thesis
      using fin
      by simp (smt (verit) Max_insert2 \<tau>_mono mem_Collect_eq not_less_eq_eq order_trans)
  qed
qed

lemma LTP_code[code]: "LTP \<sigma> t = (if t < \<tau> \<sigma> 0
  then Code.abort (STR ''LTP: undefined'') (\<lambda>_. LTP \<sigma> t)
  else LTP_rec \<sigma> t 0)"
  using LTP_rec_sound[of \<sigma> t 0]
  by (auto simp: LTP_def insert_absorb simp del: LTP_rec.simps)

code_deps LTP

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
end

derive (eq) ceq enat

instantiation enat :: set_impl begin
definition set_impl_enat :: "(enat, set_impl) phantom" where
  "set_impl_enat = phantom set_RBT"

instance ..
end

definition [code del]: "comparator_sproof' = comparator_sproof ccomp"
definition [code del]: "comparator_vproof' = comparator_vproof ccomp"
definition comparator_set' :: "'a :: ccompare set \<Rightarrow> 'a set \<Rightarrow> order" where [code del]: "comparator_set' = comparator_set ccomp"

lemma comparator_set'_code[code]:
  "(comparator_set' :: 'a :: ccompare set \<Rightarrow> 'a set \<Rightarrow> order) =
   (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort STR ''comparator_set: ccompare = None'' (\<lambda>_. comparator_set') | _ \<Rightarrow> ccomp)"
  unfolding comparator_set'_def comparator_set_def cless_eq_set_def cless_set_def ccompare_set_def
  by (auto simp: ID_Some split: option.splits)

lemmas comparator_sproof'_code[code] =
   comparator_sproof.simps[of ccomp, unfolded comparator_list'_map2 comparator_list'_map comparator_list'_vals_map_part,
     folded comparator_sproof'_def comparator_vproof'_def comparator_set'_def]
lemmas comparator_vproof'_code[code] =
   comparator_vproof.simps[of ccomp, unfolded comparator_list'_map2 comparator_list'_map comparator_list'_vals_map_part,
     folded comparator_sproof'_def comparator_vproof'_def comparator_set'_def]

lemma ccompare_sproof_code[code]: "CCOMPARE('a::ccompare sproof) = (case ID CCOMPARE('a) of None \<Rightarrow> None | Some comp_'a \<Rightarrow> Some comparator_sproof')"
  by (auto simp: ccompare_sproof_def comparator_sproof'_def split: option.splits)
lemma ccompare_vproof_code[code]: "CCOMPARE('a::ccompare vproof) = (case ID CCOMPARE('a) of None \<Rightarrow> None | Some comp_'a \<Rightarrow> Some comparator_vproof')"
  by (auto simp: ccompare_vproof_def comparator_vproof'_def split: option.splits)

lemma map_part_code[code]: "Rep_part (map_part f xs) = map (map_prod id f) (Rep_part xs)"
  using Rep_part[of xs]
  by (auto simp: map_part_def intro!: Abs_part_inverse)

instantiation nat :: default begin
definition default_nat :: nat where "default_nat = 0"
instance proof qed
end

instantiation list :: (type) default begin
definition default_list :: "'a list" where "default_list = []"
instance proof qed
end

derive (no) ceq MFOTL.trm
derive (monad) set_impl MFOTL.trm
derive (no) ceq MFOTL.formula
derive (no) ccompare MFOTL.formula
derive (monad) set_impl MFOTL.formula

definition execute_trivial_opt where
 "execute_trivial_opt \<sigma> vars i \<phi> = Monitor.opt \<sigma> (\<lambda>p1 p2. (p_pred (\<lambda> _. 1) p1) \<le> (p_pred (\<lambda> _. 1) p2)) vars i \<phi>"

definition mytrace :: "nat MFOTL.trace" where 
  "mytrace = trace_of_list [({(''p'', [1::nat])}, 0::nat)]"

value "execute_trivial_opt mytrace [''x''] (0::nat) (MFOTL.Pred ''p'' [MFOTL.Var ''x''] :: nat MFOTL.formula)"

definition mytrace2 :: "string MFOTL.trace" where 
  "mytrace2 = trace_of_list
     [({(''p'', [''Dmitriy'', ''Traytel'']), (''p'', [''Jonathan'', ''Munive'']),
        (''q'', [''Munive'']), (''q'', [''Lima''])}, 0::nat),
      ({(''p'', [''Leonardo'', ''Lima'']), (''q'', [''Lima''])}, 0::nat)]"

definition phi2 where
  "phi2 = MFOTL.Exists ''last''
    (MFOTL.And (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])
       (MFOTL.Pred ''q'' [MFOTL.Var ''last'']))"

definition phi3 where
  "phi3 = MFOTL.Forall ''last'' (MFOTL.Imp (MFOTL.Pred ''q'' [MFOTL.Var ''last''])
    (MFOTL.Exists ''first'' (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])))"


value "execute_trivial_opt mytrace2 [''first'', ''last''] 0 (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])"
value "execute_trivial_opt mytrace2 [''first'', ''last''] 0 (MFOTL.Pred ''q'' [MFOTL.Var ''last''])"
value "execute_trivial_opt mytrace2 [''first'', ''last''] 1 (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])"
value "execute_trivial_opt mytrace2 [''first'', ''last''] 1 (MFOTL.Pred ''q'' [MFOTL.Var ''last''])"
value "execute_trivial_opt mytrace2 [''first'', ''last''] 0 (MFOTL.And (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last'']) (MFOTL.Pred ''q'' [MFOTL.Var ''last'']))"
value "execute_trivial_opt mytrace2 [''first'', ''last''] 1 (MFOTL.And (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last'']) (MFOTL.Pred ''q'' [MFOTL.Var ''last'']))"
value "execute_trivial_opt mytrace2 [''first''] 0 phi2"
value "execute_trivial_opt mytrace2 [''first''] 1 phi2"
value "execute_trivial_opt mytrace2 [] 0 phi3"
value "execute_trivial_opt mytrace2 [] 1 phi3"

lift_definition lookup_part :: "('d, 'a) part \<Rightarrow> 'd \<Rightarrow> 'a" is "\<lambda>xs d. snd (the (find (\<lambda>(D, _). d \<in> D) xs))" .

lemma lookup_part_Vals[simp]: "lookup_part part d \<in> Vals part"
  apply transfer
  subgoal for xs d
    apply (cases "find (\<lambda>(D, _). d \<in> D) xs")
     apply (auto simp: partition_on_def find_None_iff find_Some_iff image_iff)
    apply (metis UNIV_I UN_iff prod.collapse)
    apply (metis (no_types, lifting) find_Some_iff nth_mem option.sel prod.simps(2))
    done
  done

lemma size_lookup_part_estimation[termination_simp]: "size (lookup_part part d) < Suc (size_part (\<lambda>_. 0) size part)"
  unfolding less_Suc_eq_le
  by (rule size_part_estimation'[OF _ order_refl]) simp

lemma subsvals_part_estimation[termination_simp]: "(D, e) \<in> set (subsvals part) \<Longrightarrow> size e < Suc (size_part (\<lambda>_. 0) size part)"
  unfolding less_Suc_eq_le
  by (rule size_part_estimation'[OF _ order_refl], transfer)
    (force simp: image_iff)
  

fun check_one where
  "check_one \<sigma> v \<phi> (Leaf p) = (case p of Inl sp \<Rightarrow> s_check \<sigma> v \<phi> sp | Inr vp \<Rightarrow> v_check \<sigma> v \<phi> vp)"
| "check_one \<sigma> v \<phi> (Node x part) = check_one \<sigma> v \<phi> (lookup_part part (v x))"

fun check_all_aux where
  "check_all_aux \<sigma> vs \<phi> (Leaf p) = (case p of Inl sp \<Rightarrow> s_check_exec \<sigma> vs \<phi> sp | Inr vp \<Rightarrow> v_check_exec \<sigma> vs \<phi> vp)"
| "check_all_aux \<sigma> vs \<phi> (Node x part) = (\<forall>(D, e) \<in> set (subsvals part). check_all_aux \<sigma> (vs(x := D)) \<phi> e)"

definition "check_all \<sigma> \<phi> e = check_all_aux \<sigma> (\<lambda>_. UNIV) \<phi> e"

(*does not work yet, probably due to the Pred case (needs a rewrite)*)
value "check_one mytrace2 (\<lambda>_. default) phi3 (execute_trivial_opt mytrace2 [] 0 phi3)"
value "check_all mytrace2 phi3 (execute_trivial_opt mytrace2 [] 0 phi3)"

end