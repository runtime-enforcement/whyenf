theory Monitor_Code
  imports Explanator2.Monitor "HOL-Library.Code_Target_Nat" Containers.Containers
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
  where "is_valid = p_check"

declare MFOTL.future_bounded.simps[code]

(* context 
  fixes \<sigma> :: "'d :: linorder MFOTL.trace" and
  wqo :: "'d proof \<Rightarrow> 'd proof \<Rightarrow> bool"
begin

lemma opt_code[code]: "optimal vs i \<phi> p = (if MFOTL.future_bounded \<phi> then
  valid \<sigma> i \<phi> p \<and> wqo p (opt vars i \<phi>) else Code.abort (STR ''opt: formula is not future bounded'') (\<lambda>_. optimal i \<phi> p))"
  using alg_optimal[of \<phi> i] trans_wqo
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
  apply(relation "measures [case_sum size size, case_sum (\<lambda>x. Suc 0) (\<lambda>x. 0), case_sum (\<lambda>x. 0) (\<lambda>x. Suc 0)]")
  apply simp_all
  sorry

definition p_pred :: "'d proof \<Rightarrow> nat" where
  "p_pred = case_sum s_pred v_pred"

end

(* definition execute_trivial_opt where
 "execute_trivial_opt \<sigma> vs i \<phi> p = Monitor.opt \<sigma> (\<lambda> _. 1) vs i \<phi> p" *)

end