(*<*)
theory Monitor
  imports Proof_System "HOL-Library.Simps_Case_Conv" 
begin
(*>*)

lift_definition part_hd :: "('d, 'a) part \<Rightarrow> 'a" is "snd \<circ> hd" .

lemma size_part_hd_estimation[termination_simp]: "size (part_hd part) < Suc (size_part (\<lambda>_. 0) size part)"
  apply transfer
  apply (simp add: size_list_conv_sum_list)
  sorry

lemma size_last_estimation[termination_simp]: "xs \<noteq> [] \<Longrightarrow> size (last xs) < size_list size xs"
  by (induct xs) auto

fun s_at :: "'d sproof \<Rightarrow> nat" and 
  v_at :: "'d vproof \<Rightarrow> nat" where
  "s_at (STT i) = i"
| "s_at (SPred i _ _) = i"
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

context fixes \<sigma> :: "'d MFOTL.trace"

begin

fun s_check :: "'d MFOTL.env \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd sproof \<Rightarrow> bool"
  and v_check :: "'d MFOTL.env \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd vproof \<Rightarrow> bool" where
  "s_check v f p = (case (f, p) of
    (MFOTL.TT, STT i) \<Rightarrow> True
  | (MFOTL.Pred r ts, SPred i s ts') \<Rightarrow> 
    (r = s \<and> ts = ts' \<and> (r, MFOTL.eval_trms v ts) \<in> \<Gamma> \<sigma> i)
  | (MFOTL.Neg \<phi>, SNeg vp) \<Rightarrow> v_check v \<phi> vp
  | (MFOTL.Or \<phi> \<psi>, SOrL sp1) \<Rightarrow> s_check v \<phi> sp1
  | (MFOTL.Or \<phi> \<psi>, SOrR sp2) \<Rightarrow> s_check v \<psi> sp2
  | (MFOTL.And \<phi> \<psi>, SAnd sp1 sp2) \<Rightarrow> s_check v \<phi> sp1 \<and> s_check v \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (MFOTL.Imp \<phi> \<psi>, SImpL vp1) \<Rightarrow> v_check v \<phi> vp1
  | (MFOTL.Imp \<phi> \<psi>, SImpR sp2) \<Rightarrow> s_check v \<psi> sp2
  | (MFOTL.Iff \<phi> \<psi>, SIffSS sp1 sp2) \<Rightarrow> s_check v \<phi> sp1 \<and> s_check v \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (MFOTL.Iff \<phi> \<psi>, SIffVV vp1 vp2) \<Rightarrow> v_check v \<phi> vp1 \<and> v_check v \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (MFOTL.Exists x \<phi>, SExists y val sp) \<Rightarrow> (x = y \<and> s_check (v (x := val)) \<phi> sp)
  | (MFOTL.Forall x \<phi>, SForall y sp_part) \<Rightarrow> (x = y \<and> (\<forall>(sub, sp) \<in> SubsVals sp_part. \<forall>z \<in> sub. s_check (v (x := z)) \<phi> sp))
  | (MFOTL.Prev I \<phi>, SPrev sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SPrev sp) in 
    i = j+1 \<and> mem (\<Delta> \<sigma> i) I \<and> s_check v \<phi> sp)
  | (MFOTL.Next I \<phi>, SNext sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SNext sp) in
    j = i+1 \<and> mem (\<Delta> \<sigma> j) I \<and> s_check v \<phi> sp)
  | (MFOTL.Once I \<phi>, SOnce i sp) \<Rightarrow> 
    (let j = s_at sp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> s_check v \<phi> sp)
  | (MFOTL.Eventually I \<phi>, SEventually i sp) \<Rightarrow> 
    (let j = s_at sp in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> s_check v \<phi> sp)
  | (MFOTL.Historically I \<phi>, SHistoricallyOut i) \<Rightarrow> 
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (MFOTL.Historically I \<phi>, SHistorically i li sps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - b))
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map s_at sps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>sp \<in> set sps. s_check v \<phi> sp))
  | (MFOTL.Always I \<phi>, SAlways i hi sps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) 
    \<and> right I \<noteq> \<infinity>
    \<and> map s_at sps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>sp \<in> set sps. s_check v \<phi> sp))
  | (MFOTL.Since \<phi> I \<psi>, SSince sp2 sp1s) \<Rightarrow>
    (let i = s_at (SSince sp2 sp1s); j = s_at sp2 in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I 
    \<and> map s_at sp1s = [j+1 ..< i+1] 
    \<and> s_check v \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check v \<phi> sp1))
  | (MFOTL.Until \<phi> I \<psi>, SUntil sp1s sp2) \<Rightarrow>
    (let i = s_at (SUntil sp1s sp2); j = s_at sp2 in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I
    \<and> map s_at sp1s = [i ..< j] \<and> s_check v \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check v \<phi> sp1))
  | ( _ , _) \<Rightarrow> False)"
| "v_check v f p = (case (f, p) of
    (MFOTL.FF, VFF i) \<Rightarrow> True
  | (MFOTL.Pred r ts, VPred i pred ts') \<Rightarrow> 
    (r = pred \<and> ts = ts' \<and> (r, map (MFOTL.eval_trm v) ts) \<notin> \<Gamma> \<sigma> i)
  | (MFOTL.Neg \<phi>, VNeg sp) \<Rightarrow> s_check v \<phi> sp
  | (MFOTL.Or \<phi> \<psi>, VOr vp1 vp2) \<Rightarrow> v_check v \<phi> vp1 \<and> v_check v \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (MFOTL.And \<phi> \<psi>, VAndL vp1) \<Rightarrow> v_check v \<phi> vp1
  | (MFOTL.And \<phi> \<psi>, VAndR vp2) \<Rightarrow> v_check v \<psi> vp2
  | (MFOTL.Imp \<phi> \<psi>, VImp sp1 vp2) \<Rightarrow> s_check v \<phi> sp1 \<and> v_check v \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (MFOTL.Iff \<phi> \<psi>, VIffSV sp1 vp2) \<Rightarrow> s_check v \<phi> sp1 \<and> v_check v \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (MFOTL.Iff \<phi> \<psi>, VIffVS vp1 sp2) \<Rightarrow> v_check v \<phi> vp1 \<and> s_check v \<psi> sp2 \<and> v_at vp1 = s_at sp2
  | (MFOTL.Exists x \<phi>, VExists y vp_part) \<Rightarrow> (x = y \<and> (\<forall>(sub, vp) \<in> SubsVals vp_part. \<forall>z \<in> sub. v_check (v (x := z)) \<phi> vp))
  | (MFOTL.Forall x \<phi>, VForall y val vp) \<Rightarrow> (x = y \<and> v_check (v (x := val)) \<phi> vp)
  | (MFOTL.Prev I \<phi>, VPrev vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VPrev vp) in
    i = j+1 \<and> v_check v \<phi> vp)
  | (MFOTL.Prev I \<phi>, VPrevZ) \<Rightarrow>
    v_at (VPrevZ::'d vproof) = 0
  | (MFOTL.Prev I \<phi>, VPrevOutL i) \<Rightarrow>
    i > 0 \<and> \<Delta> \<sigma> i < left I
  | (MFOTL.Prev I \<phi>, VPrevOutR i) \<Rightarrow>
    i > 0 \<and> enat (\<Delta> \<sigma> i) > right I
  | (MFOTL.Next I \<phi>, VNext vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VNext vp) in
    j = i+1 \<and> v_check v \<phi> vp)
  | (MFOTL.Next I \<phi>, VNextOutL i) \<Rightarrow>
    \<Delta> \<sigma> (i+1) < left I
  | (MFOTL.Next I \<phi>, VNextOutR i) \<Rightarrow>
    enat (\<Delta> \<sigma> (i+1)) > right I
  | (MFOTL.Once I \<phi>, VOnceOut i) \<Rightarrow> 
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (MFOTL.Once I \<phi>, VOnce i li vps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp \<in> set vps. v_check v \<phi> vp))
  | (MFOTL.Eventually I \<phi>, VEventually i hi vps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>vp \<in> set vps. v_check v \<phi> vp))
  | (MFOTL.Historically I \<phi>, VHistorically i vp) \<Rightarrow> 
    (let j = v_at vp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> v_check v \<phi> vp)
  | (MFOTL.Always I \<phi>, VAlways i vp) \<Rightarrow> 
    (let j = v_at vp
    in j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> v_check v \<phi> vp)
  | (MFOTL.Since \<phi> I \<psi>, VSinceOut i) \<Rightarrow>
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (MFOTL.Since \<phi> I \<psi>, VSince i vp1 vp2s) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> ETP_p \<sigma> i b \<le> j) \<and> j \<le> i
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [j ..< (LTP_p \<sigma> i I) + 1] \<and> v_check v \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | (MFOTL.Since \<phi> I \<psi>, VSinceInf i li vp2s) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | (MFOTL.Until \<phi> I \<psi>, VUntil i vp2s vp1) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> j \<le> LTP_f \<sigma> i b) \<and> i \<le> j
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< j + 1] \<and> v_check v \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | (MFOTL.Until \<phi> I \<psi>, VUntilInf i hi vp2s) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< hi + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | ( _ , _) \<Rightarrow> False)"

declare s_check.simps[simp del] v_check.simps[simp del]
simps_of_case s_check_simps[simp, code]: s_check.simps[unfolded prod.case] (splits: MFOTL.formula.split sproof.split)
simps_of_case v_check_simps[simp, code]: v_check.simps[unfolded prod.case] (splits: MFOTL.formula.split vproof.split)

primrec fst_pos :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option" 
  where "fst_pos [] x = None" 
  | "fst_pos (y#ys) x = (if x = y then Some 0 else 
      (case fst_pos ys x of None \<Rightarrow> None | Some n \<Rightarrow> Some (Suc n)))"

lemma fst_pos_None_iff: "fst_pos xs x = None \<longleftrightarrow> x \<notin> set xs"
  by (induct xs arbitrary: x; force split: option.splits)

lemma nth_fst_pos: "x \<in> set xs \<Longrightarrow> xs ! (the (fst_pos xs x)) = x"
  by (induct xs arbitrary: x; fastforce simp: fst_pos_None_iff split: option.splits)

primrec positions :: "'a list \<Rightarrow> 'a \<Rightarrow> nat list"
  where "positions [] x = []" 
  | "positions (y#ys) x = (if x = y then 0 # (map Suc (positions ys x)) else map Suc (positions ys x))"

lemma positions_eq_nil_iff: "positions xs x = [] \<longleftrightarrow> x \<notin> set xs"
  by (induct xs) simp_all

lemma positions_nth: "n \<in> set (positions xs x) \<Longrightarrow> xs ! n = x"
  by (induct xs arbitrary: n x)
    (auto simp: positions_eq_nil_iff[symmetric] split: if_splits)

lemma positions_length: "n \<in> set (positions xs x) \<Longrightarrow> n < length xs"
  by (induct xs arbitrary: n x)
    (auto simp: positions_eq_nil_iff[symmetric] split: if_splits)

lemma positions_nth_cong: 
  "m \<in> set (positions xs x) \<Longrightarrow> n \<in> set (positions xs x) \<Longrightarrow> xs ! n = xs ! m"
  using positions_nth[of _ xs x] by simp

lemma fst_pos_in_positions: "x \<in> set xs \<Longrightarrow> the (fst_pos xs x) \<in> set (positions xs x)"
  by (induct xs arbitrary: x, simp)
    (fastforce simp: hd_map fst_pos_None_iff split: option.splits)

lemma hd_positions_eq_fst_pos: "x \<in> set xs \<Longrightarrow> hd (positions xs x) = the (fst_pos xs x)"
  by (induct xs arbitrary: x)
    (auto simp: hd_map fst_pos_None_iff positions_eq_nil_iff split: option.splits)

lemma sorted_positions: "sorted (positions xs x)"
  apply (induct xs arbitrary: x)
  by simp_all (simp_all add: sorted_iff_nth_Suc)

lemma Min_sorted_list: "sorted xs \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> Min (set xs) = hd xs"
  by (induct xs)
    (auto simp: Min_insert2)

lemma Min_positions: "x \<in> set xs \<Longrightarrow> Min (set (positions xs x)) = the (fst_pos xs x)"
  by (auto simp: Min_sorted_list[OF sorted_positions] 
      positions_eq_nil_iff hd_positions_eq_fst_pos)

definition "compatible X vs v \<longleftrightarrow> (\<forall>x\<in>X. v x \<in> vs x)"

definition "compatible_vals X vs = {v. \<forall>x \<in> X. v x \<in> vs x}"

lemma compatible_iff_in_compatible_vals: 
  "compatible X vs v \<longleftrightarrow> v \<in> compatible_vals X vs"
  by (auto simp: compatible_def compatible_vals_def)

primrec mk_values :: "('b MFOTL.trm \<times> 'a set) list \<Rightarrow> 'a list set" 
  where "mk_values [] = {[]}" 
  | "mk_values (T # Ts) = (case T of 
      (MFOTL.Var x, X) \<Rightarrow> 
        let terms = map fst Ts in
        if MFOTL.Var x \<in> set terms then
          let fst_pos = hd (positions terms (MFOTL.Var x)) in (\<lambda>xs. (xs ! fst_pos) # xs) ` (mk_values Ts)
        else set_Cons X (mk_values Ts)
    | (MFOTL.Const a, X) \<Rightarrow> set_Cons X (mk_values Ts))"

lemma mk_values_nempty: 
  "{} \<notin> set (map snd tXs) \<Longrightarrow> mk_values tXs \<noteq> {}"
  by (induct tXs)
    (auto simp: set_Cons_def image_iff split: MFOTL.trm.splits if_splits)

lemma mk_values_not_Nil: 
  "{} \<notin> set (map snd tXs) \<Longrightarrow> tXs \<noteq> [] \<Longrightarrow> vs \<in> mk_values tXs \<Longrightarrow> vs \<noteq> []"
  by (induct tXs)
    (auto simp: set_Cons_def image_iff split: MFOTL.trm.splits if_splits)

lemma mk_values_nth_cong: "MFOTL.Var x \<in> set (map fst tXs) 
  \<Longrightarrow> n \<in> set (positions (map fst tXs) (MFOTL.Var x))
  \<Longrightarrow> m \<in> set (positions (map fst tXs) (MFOTL.Var x))
  \<Longrightarrow> vs \<in> mk_values tXs
  \<Longrightarrow> vs ! n = vs ! m"
  apply (induct tXs arbitrary: n m vs x)
   apply simp
  subgoal for tX tXs n m v x
    apply (cases "fst tX = MFOTL.Var x"; cases "MFOTL.Var x \<in> set (map fst tXs)")
    subgoal
      apply (simp add: image_iff split: prod.splits)
      apply (elim disjE; simp?)
        apply (metis hd_in_set length_greater_0_conv length_pos_if_in_set nth_Cons_0 nth_Cons_Suc)
       apply (metis hd_in_set length_greater_0_conv length_pos_if_in_set nth_Cons_0 nth_Cons_Suc)
      apply (metis nth_Cons_Suc)
      done
    subgoal
      by (simp add: image_iff split: prod.splits)
        (smt (verit, ccfv_threshold) empty_iff empty_set in_set_conv_nth length_map nth_map positions_eq_nil_iff)
    subgoal
      apply (clarsimp simp: image_iff set_Cons_def split: MFOTL.trm.splits)
      by (split if_splits; simp add: image_iff set_Cons_def)
        (metis fst_conv nth_Cons_Suc)+
    by clarsimp
  done

fun s_check_exec :: "'d MFOTL.envset \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd sproof \<Rightarrow> bool"
  and v_check_exec :: "'d MFOTL.envset \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd vproof \<Rightarrow> bool" where
  "s_check_exec vs f p = (case (f, p) of
    (MFOTL.TT, STT i) \<Rightarrow> True
  | (MFOTL.Pred r ts, SPred i s ts') \<Rightarrow> 
    (r = s \<and> ts = ts' \<and> {r} \<times> mk_values (MFOTL.eval_trms_set vs ts) \<subseteq> \<Gamma> \<sigma> i)
  | (MFOTL.Neg \<phi>, SNeg vp) \<Rightarrow> v_check_exec vs \<phi> vp
  | (MFOTL.Or \<phi> \<psi>, SOrL sp1) \<Rightarrow> s_check_exec vs \<phi> sp1
  | (MFOTL.Or \<phi> \<psi>, SOrR sp2) \<Rightarrow> s_check_exec vs \<psi> sp2
  | (MFOTL.And \<phi> \<psi>, SAnd sp1 sp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> s_check_exec vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (MFOTL.Imp \<phi> \<psi>, SImpL vp1) \<Rightarrow> v_check_exec vs \<phi> vp1
  | (MFOTL.Imp \<phi> \<psi>, SImpR sp2) \<Rightarrow> s_check_exec vs \<psi> sp2
  | (MFOTL.Iff \<phi> \<psi>, SIffSS sp1 sp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> s_check_exec vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (MFOTL.Iff \<phi> \<psi>, SIffVV vp1 vp2) \<Rightarrow> v_check_exec vs \<phi> vp1 \<and> v_check_exec vs \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (MFOTL.Exists x \<phi>, SExists y val sp) \<Rightarrow> (x = y \<and> s_check_exec (vs (x := {val})) \<phi> sp)
  | (MFOTL.Forall x \<phi>, SForall y sp_part) \<Rightarrow> (x = y \<and> (\<forall>(sub, sp) \<in> SubsVals sp_part. s_check_exec (vs (x := sub)) \<phi> sp))
  | (MFOTL.Prev I \<phi>, SPrev sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SPrev sp) in 
    i = j+1 \<and> mem (\<Delta> \<sigma> i) I \<and> s_check_exec vs \<phi> sp)
  | (MFOTL.Next I \<phi>, SNext sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SNext sp) in
    j = i+1 \<and> mem (\<Delta> \<sigma> j) I \<and> s_check_exec vs \<phi> sp)
  | (MFOTL.Once I \<phi>, SOnce i sp) \<Rightarrow> 
    (let j = s_at sp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> s_check_exec vs \<phi> sp)
  | (MFOTL.Eventually I \<phi>, SEventually i sp) \<Rightarrow> 
    (let j = s_at sp in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> s_check_exec vs \<phi> sp)
  | (MFOTL.Historically I \<phi>, SHistoricallyOut i) \<Rightarrow> 
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (MFOTL.Historically I \<phi>, SHistorically i li sps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - b))
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map s_at sps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>sp \<in> set sps. s_check_exec vs \<phi> sp))
  | (MFOTL.Always I \<phi>, SAlways i hi sps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) 
    \<and> right I \<noteq> \<infinity>
    \<and> map s_at sps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>sp \<in> set sps. s_check_exec vs \<phi> sp))
  | (MFOTL.Since \<phi> I \<psi>, SSince sp2 sp1s) \<Rightarrow>
    (let i = s_at (SSince sp2 sp1s); j = s_at sp2 in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I 
    \<and> map s_at sp1s = [j+1 ..< i+1] 
    \<and> s_check_exec vs \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check_exec vs \<phi> sp1))
  | (MFOTL.Until \<phi> I \<psi>, SUntil sp1s sp2) \<Rightarrow>
    (let i = s_at (SUntil sp1s sp2); j = s_at sp2 in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I
    \<and> map s_at sp1s = [i ..< j] \<and> s_check_exec vs \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check_exec vs \<phi> sp1))
  | ( _ , _) \<Rightarrow> False)"
| "v_check_exec vs f p = (case (f, p) of
    (MFOTL.FF, VFF i) \<Rightarrow> True
  | (MFOTL.Pred r ts, VPred i pred ts') \<Rightarrow> 
    (r = pred \<and> ts = ts' \<and> {r} \<times> mk_values (map (MFOTL.eval_trm_set vs) ts) \<subseteq> - \<Gamma> \<sigma> i)
  | (MFOTL.Neg \<phi>, VNeg sp) \<Rightarrow> s_check_exec vs \<phi> sp
  | (MFOTL.Or \<phi> \<psi>, VOr vp1 vp2) \<Rightarrow> v_check_exec vs \<phi> vp1 \<and> v_check_exec vs \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (MFOTL.And \<phi> \<psi>, VAndL vp1) \<Rightarrow> v_check_exec vs \<phi> vp1
  | (MFOTL.And \<phi> \<psi>, VAndR vp2) \<Rightarrow> v_check_exec vs \<psi> vp2
  | (MFOTL.Imp \<phi> \<psi>, VImp sp1 vp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> v_check_exec vs \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (MFOTL.Iff \<phi> \<psi>, VIffSV sp1 vp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> v_check_exec vs \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (MFOTL.Iff \<phi> \<psi>, VIffVS vp1 sp2) \<Rightarrow> v_check_exec vs \<phi> vp1 \<and> s_check_exec vs \<psi> sp2 \<and> v_at vp1 = s_at sp2
  | (MFOTL.Exists x \<phi>, VExists y vp_part) \<Rightarrow> (x = y \<and> (\<forall>(sub, vp) \<in> SubsVals vp_part. v_check_exec (vs (x := sub)) \<phi> vp))
  | (MFOTL.Forall x \<phi>, VForall y val vp) \<Rightarrow> (x = y \<and> v_check_exec (vs (x := {val})) \<phi> vp)
  | (MFOTL.Prev I \<phi>, VPrev vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VPrev vp) in
    i = j+1 \<and> v_check_exec vs \<phi> vp)
  | (MFOTL.Prev I \<phi>, VPrevZ) \<Rightarrow>
    v_at (VPrevZ::'d vproof) = 0
  | (MFOTL.Prev I \<phi>, VPrevOutL i) \<Rightarrow>
    i > 0 \<and> \<Delta> \<sigma> i < left I
  | (MFOTL.Prev I \<phi>, VPrevOutR i) \<Rightarrow>
    i > 0 \<and> enat (\<Delta> \<sigma> i) > right I
  | (MFOTL.Next I \<phi>, VNext vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VNext vp) in
    j = i+1 \<and> v_check_exec vs \<phi> vp)
  | (MFOTL.Next I \<phi>, VNextOutL i) \<Rightarrow>
    \<Delta> \<sigma> (i+1) < left I
  | (MFOTL.Next I \<phi>, VNextOutR i) \<Rightarrow>
    enat (\<Delta> \<sigma> (i+1)) > right I
  | (MFOTL.Once I \<phi>, VOnceOut i) \<Rightarrow> 
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (MFOTL.Once I \<phi>, VOnce i li vps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp \<in> set vps. v_check_exec vs \<phi> vp))
  | (MFOTL.Eventually I \<phi>, VEventually i hi vps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>vp \<in> set vps. v_check_exec vs \<phi> vp))
  | (MFOTL.Historically I \<phi>, VHistorically i vp) \<Rightarrow> 
    (let j = v_at vp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> v_check_exec vs \<phi> vp)
  | (MFOTL.Always I \<phi>, VAlways i vp) \<Rightarrow> 
    (let j = v_at vp
    in j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> v_check_exec vs \<phi> vp)
  | (MFOTL.Since \<phi> I \<psi>, VSinceOut i) \<Rightarrow>
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (MFOTL.Since \<phi> I \<psi>, VSince i vp1 vp2s) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> ETP_p \<sigma> i b \<le> j) \<and> j \<le> i
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [j ..< (LTP_p \<sigma> i I) + 1] \<and> v_check_exec vs \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | (MFOTL.Since \<phi> I \<psi>, VSinceInf i li vp2s) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | (MFOTL.Until \<phi> I \<psi>, VUntil i vp2s vp1) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> j \<le> LTP_f \<sigma> i b) \<and> i \<le> j
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< j + 1] \<and> v_check_exec vs \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | (MFOTL.Until \<phi> I \<psi>, VUntilInf i hi vp2s) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< hi + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | ( _ , _) \<Rightarrow> False)"

declare s_check_exec.simps[simp del] v_check_exec.simps[simp del]
simps_of_case s_check_exec_simps[simp, code]: s_check_exec.simps[unfolded prod.case] (splits: MFOTL.formula.split sproof.split)
simps_of_case v_check_exec_simps[simp, code]: v_check_exec.simps[unfolded prod.case] (splits: MFOTL.formula.split vproof.split)

lemma check_soundness:
  "s_check v \<phi> sp \<Longrightarrow> SAT \<sigma> v (s_at sp) \<phi>"
  "v_check v \<phi> vp \<Longrightarrow> VIO \<sigma> v (v_at vp) \<phi>"
  oops

unbundle MFOTL_notation \<comment> \<open> enable notation \<close>

lemma mk_values_sound: "as \<in> mk_values (MFOTL.eval_trms_set vs ts) 
  \<Longrightarrow> \<exists>v\<in>compatible_vals (fv (p \<dagger> ts)) vs. as = MFOTL.eval_trms v ts"
proof (induct ts arbitrary: as vs)
  let ?evals = MFOTL.eval_trms_set
    and ?eval = "MFOTL.eval_trm_set"
  case (Cons t ts)
  show ?case
  proof(cases t)
    case (Var x)
    let ?Ts = "?evals vs ts"
    have "?evals vs (t # ts) = (\<^bold>v x, vs x) # ?Ts"
      using Var by (simp add: MFOTL.eval_trms_set_def)
    show ?thesis
    proof (cases "\<^bold>v x \<in> set ts")
      case True
      then obtain n where n_in: "n \<in> set (positions ts (\<^bold>v x))"
        and nth_n: "ts ! n = \<^bold>v x"
        by (meson fst_pos_in_positions nth_fst_pos)
      hence n_in': "n \<in> set (positions (map fst ?Ts) (\<^bold>v x))"
        by (induct ts arbitrary: n)
          (auto simp: MFOTL.eval_trms_set_def split: if_splits)
      have key: "\<^bold>v x \<in> set (map fst ?Ts)"
        using True by (induct ts)
          (auto simp: MFOTL.eval_trms_set_def)
      then obtain a as' 
        where as_head: "as' ! (hd (positions (map fst ?Ts) (\<^bold>v x))) = a"
          and as_tail: "as' \<in> mk_values (MFOTL.eval_trms_set vs ts)" 
          and as_shape: "as = a # as'"
        using Cons(2) 
        by (clarsimp simp add: MFOTL.eval_trms_set_def Var image_iff)
      obtain v where v_hyps: "v \<in> compatible_vals (fv (p \<dagger> ts)) vs"
        "as' = MFOTL.eval_trms v ts"
        using Cons(1)[OF as_tail] by blast
      hence as'_nth: "as' ! n = v x"
        using nth_n positions_length[OF n_in]
        by (simp add: MFOTL.eval_trms_def)
      have evals_neq_Nil: "?evals vs ts \<noteq> []"
        using key by auto
      moreover have "positions (map fst (MFOTL.eval_trms_set vs ts)) (\<^bold>v x) \<noteq> []"
        using positions_eq_nil_iff[of "map fst ?Ts" "\<^bold>v x"] key
        by fastforce
      ultimately have as_hyp: "a = as' ! n"
        using mk_values_nth_cong[OF key hd_in_set n_in' as_tail] as_head  by blast
      thus ?thesis
        using Var as_shape True v_hyps as'_nth
        by (auto simp: compatible_vals_def MFOTL.eval_trms_def intro!: exI[of _ v])
    next
      case False
      hence "\<^bold>v x \<notin> set (map fst ?Ts)"
        using Var
        apply (induct ts arbitrary: x)
        by (auto simp: MFOTL.eval_trms_set_def image_iff)
          (metis eq_fst_iff eval_trm_set.simps(1) eval_trm_set.simps(2) trm.exhaust)
      then show ?thesis 
        using Cons(2) Var False
        apply (clarsimp simp: MFOTL.eval_trms_set_def set_Cons_def 
          MFOTL.eval_trms_def compatible_vals_def split: )
        subgoal for a as'
          using Cons(1)[of as' vs] 
          apply (clarsimp simp: MFOTL.eval_trms_set_def MFOTL.eval_trms_def compatible_vals_def)
          apply (rule_tac x="v(x := a)" in exI)
          apply clarsimp
          apply (rule eval_trm_fv_cong)
          apply clarsimp
          subgoal for v t'
            by (rule trm.exhaust[of t'])
              auto
          done
        done
    qed
  next
    case (Const c)
    then show ?thesis
      using Cons(1)[of _ vs] Cons(2)
      by (auto simp: MFOTL.eval_trms_set_def set_Cons_def 
          MFOTL.eval_trms_def compatible_def)
  qed
qed (simp add: MFOTL.eval_trms_set_def MFOTL.eval_trms_def compatible_vals_def)
 
lemma mk_values_complete: "as = MFOTL.eval_trms v ts 
  \<Longrightarrow> v \<in> compatible_vals (fv (p \<dagger> ts)) vs
  \<Longrightarrow> as \<in> mk_values (MFOTL.eval_trms_set vs ts)"
  sorry

lemma check_exec_check:
  assumes "compatible_vals (fv \<phi>) vs \<noteq> {}"
  shows "s_check_exec vs \<phi> sp \<longleftrightarrow> (\<forall>v \<in> compatible_vals (fv \<phi>) vs. s_check v \<phi> sp)" 
    and "v_check_exec vs \<phi> vp \<longleftrightarrow> (\<forall>v \<in> compatible_vals (fv \<phi>) vs. v_check v \<phi> vp)"
  using assms
proof (induct \<phi> arbitrary: vs sp vp)
  case TT
  {
    case 1
    then show ?case
      by (cases sp)
        (auto simp: compatible_def)
  next
    case 2
    then show ?case 
      by (auto simp: compatible_def)
  }
next
  case FF
  {
    case 1
    then show ?case 
      by (cases sp)
        (auto simp: compatible_def)
  next
    case 2
    then show ?case 
      by (cases vp)
        (auto simp: compatible_def)
  }
next
  case (Pred p ts)
  {
    case 1
    thus ?case
      apply (cases sp; clarsimp simp: subset_eq simp del: fv.simps)
      apply (intro iffI conjI impI allI ballI)
           apply clarsimp
          apply clarsimp
         apply (elim conjE, clarsimp simp del: fv.simps)
      using mk_values_complete apply force
      using mk_values_sound by blast+
  next
    case 2
    then show ?case 
      apply (cases vp; clarsimp simp: subset_eq simp del: fv.simps)
      apply (intro iffI conjI impI allI ballI)
           apply clarsimp
           apply clarsimp
         apply (elim conjE, clarsimp simp del: fv.simps)
      apply (metis MFOTL.eval_trms_def MFOTL.eval_trms_set_def mk_values_complete)
      using mk_values_sound apply blast
        using mk_values_sound apply blast
        by (metis MFOTL.eval_trms_def MFOTL.eval_trms_set_def mk_values_sound)
  }
next
  case (Neg \<phi>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Or \<phi>1 \<phi>2)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (And \<phi>1 \<phi>2)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Imp \<phi>1 \<phi>2)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Iff \<phi>1 \<phi>2)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Exists x1 \<phi>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Forall x1 \<phi>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Prev x1 \<phi>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Next x1 \<phi>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Once x1 \<phi>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Historically x1 \<phi>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Eventually x1 \<phi>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Always x1 \<phi>)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Since \<phi>1 x2 \<phi>2)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
next
  case (Until \<phi>1 x2 \<phi>2)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  }
qed
(* proof (induct vs \<phi> sp and vs \<phi> vp arbitrary: vs rule: s_check_exec_v_check_exec.induct) *)

unbundle MFOTL_no_notation \<comment> \<open> disable notation \<close>

definition AD where 
  "AD \<phi> i = (\<Union> k < enat (i+1) + (MFOTL.future_reach \<phi>). \<Union> (set ` snd ` \<Gamma> \<sigma> (the_enat k)))"

lemma check_cong:
  assumes "(\<forall>x \<in> MFOTL.fv \<phi>. v1 x = v2 x \<or> v1 x \<notin> AD \<phi> i \<and> v2 x \<notin> AD \<phi> i)"
  shows "(s_at sp = i \<Longrightarrow> s_check v1 \<phi> sp \<longleftrightarrow> s_check v2 \<phi> sp)"
    "(v_at vp = i \<Longrightarrow> v_check v1 \<phi> vp \<longleftrightarrow> v_check v2 \<phi> vp)"
proof (induction v1 \<phi> sp and v1 \<phi> vp rule: s_check_v_check.induct)
  case (1 v f p)
  show ?case
  proof (cases p)
    case (SPred x21 x22 x23)
    then show ?thesis sorry
  next
    case (SNeg x3)
    then show ?thesis sorry
  next
    case (SOrL x4)
    then show ?thesis sorry
  next
    case (SOrR x5)
    then show ?thesis sorry
  next
    case (SAnd x61 x62)
    then show ?thesis sorry
  next
    case (SImpL x7)
    then show ?thesis sorry
  next
    case (SImpR x8)
    then show ?thesis sorry
  next
    case (SIffSS x91 x92)
    then show ?thesis sorry
  next
    case (SIffVV x101 x102)
    then show ?thesis sorry
  next
    case (SExists x111 x112 x113)
    then show ?thesis sorry
  next
    case (SForall x121 x122)
    then show ?thesis sorry
  next
    case (SPrev x13)
    then show ?thesis sorry
  next
    case (SNext x14)
    then show ?thesis sorry
  next
    case (SOnce x151 x152)
    then show ?thesis sorry
  next
    case (SEventually x161 x162)
    then show ?thesis sorry
  next
    case (SHistorically x171 x172 x173)
    then show ?thesis sorry
  next
    case (SHistoricallyOut x18)
    then show ?thesis sorry
  next
    case (SAlways x191 x192 x193)
    then show ?thesis sorry
  next
    case (SSince x201 x202)
    then show ?thesis sorry
  next
    case (SUntil x211 x212)
    then show ?thesis sorry
  qed (cases f; simp_all)
next
  case (2 v f p)
  then show ?case sorry
qed

setup_lifting type_definition_part

lift_definition trivial_part :: "'pt \<Rightarrow> ('d, 'pt) part" is "\<lambda>pt. [(UNIV, pt)]"
  by (simp add: partition_on_space)

lemma part_hd_trivial[simp]: "part_hd (trivial_part pt) = pt"
  unfolding part_hd_def
  by (transfer) simp

lemma SubsVals_trivial[simp]: "SubsVals (trivial_part pt) = {(UNIV, pt)}"
  unfolding SubsVals_def
  by (transfer) simp

lemma check_completeness:
  "(SAT \<sigma> v i \<phi> \<longrightarrow> MFOTL.future_bounded \<phi> \<longrightarrow> (\<exists>sp. s_at sp = i \<and> s_check v \<phi> sp)) \<and>
   (VIO \<sigma> v i \<phi> \<longrightarrow> MFOTL.future_bounded \<phi> \<longrightarrow> (\<exists>vp. v_at vp = i \<and> v_check v \<phi> vp))"
proof (induct v i \<phi> rule: SAT_VIO.induct)
  case (STT v i)
  then show ?case
    apply simp
    apply (rule exI[of _ "STT i"])
    apply (simp add: fun_upd_def)
    done
next
  case (VFF v i)
  then show ?case 
    apply simp
    apply (rule exI[of _ "VFF i"])
    apply (simp add: fun_upd_def)
    done
next
  case (SPred r v ts i)
  then show ?case sorry
next
  case (VPred r v ts i)
  then show ?case sorry
next
  case (SNeg v i \<phi>)
  then show ?case sorry
next
  case (VNeg v i \<phi>)
  then show ?case sorry
next
  case (SOrL v i \<phi> \<psi>)
  then show ?case sorry
next
  case (SOrR v i \<psi> \<phi>)
  then show ?case sorry
next
  case (VOr v i \<phi> \<psi>)
  then show ?case sorry
next
  case (SAnd v i \<phi> \<psi>)
  then show ?case sorry
next
  case (VAndL v i \<phi> \<psi>)
  then show ?case sorry
next
  case (VAndR v i \<psi> \<phi>)
  then show ?case sorry
next
  case (SImpL v i \<phi> \<psi>)
  then show ?case sorry
next
  case (SImpR v i \<psi> \<phi>)
  then show ?case sorry
next
  case (VImp v i \<phi> \<psi>)
  then show ?case sorry
next
  case (SIffSS v i \<phi> \<psi>)
  then show ?case sorry
next
  case (SIffVV v i \<phi> \<psi>)
  then show ?case sorry
next
  case (VIffSV v i \<phi> \<psi>)
  then show ?case sorry
next
  case (VIffVS v i \<phi> \<psi>)
  then show ?case sorry
next
  case (SExists v x i \<phi>)
  then show ?case
    apply clarsimp
    subgoal for z sp
      apply (rule exI[of _ "SExists x z sp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VExists v x i \<phi>')
  then show ?case
  proof (induction \<phi>')
    case FF
    obtain vp where vp_def: "vp = VExists x (trivial_part (VFF i))"
      by (atomize_elim) simp
    then have "v_at vp = i"
      by simp
    moreover have "v_check v (MFOTL.Exists x MFOTL.FF) vp"
      using FF vp_def
      by simp
    ultimately show ?case 
      using FF by auto
  next
    case (Pred r ts)
    {
      fix z
      have v_check_Pred_VPred: "\<And>v' vp. v_check v' (MFOTL.Pred r ts) vp \<Longrightarrow> v_at vp = i \<Longrightarrow> vp = VPred (v_at vp) r ts"
        by (elim v_check.elims; clarsimp) 
          (auto split: vproof.splits)
      obtain vp where IH_unfolded: "v_at vp = i" 
        "VIO \<sigma> (v(x := z)) i (MFOTL.Pred r ts)" 
        "v_check (v(x := z)) (MFOTL.Pred r ts) vp"
        using Pred
        by (auto simp: fun_upd_def)
      hence "vp = VPred i r ts"
        using v_check_Pred_VPred by simp
      hence "v_at (VPred i r ts) = i"  
        "v_check (v(x := z)) (MFOTL.Pred r ts) (VPred i r ts)"
        using IH_unfolded
        by simp_all
    }
    thus ?case
      unfolding Pred
      by (auto intro!: exI[of _ "VExists x (trivial_part (VPred i r ts))"])
  next
    case (Neg \<alpha>)
    thm VExists[unfolded Neg, rule_format, simplified] Neg
    {
      fix z assume "MFOTL.future_bounded (MFOTL.Neg \<alpha>)"
      (* obtain sp' :: "'d sproof" where sp'_def: "s_check v \<alpha> sp'" "s_at sp' = i"
        using VExists Neg
        apply (atomize_elim)
        sorry *)
      (* have v_check_Neg_VNeg: "\<And>v' vp. v_check v' (MFOTL.Neg \<alpha>) vp \<Longrightarrow> v_at vp = i \<Longrightarrow> vp = VNeg sp'"
        apply (elim v_check.elims) 
        apply clarsimp
        apply (auto split: vproof.splits)
        sorry *)
      then obtain vp where IH_unfolded: "v_at vp = i" 
        "VIO \<sigma> (v(x := z)) i (MFOTL.Neg \<alpha>)" 
        "v_check (v(x := z)) (MFOTL.Neg \<alpha>) vp"
        using Neg
        (* by (auto simp: fun_upd_def) *)
        sorry
      then obtain sp' where "vp = VNeg sp'"
        apply (elim v_check.elims)
        apply clarsimp
        apply (auto split: vproof.splits)
        done
      hence "v_at (VNeg sp') = i" 
        "v_check (v(x := z)) (MFOTL.Neg \<alpha>) (VNeg sp')"
        using IH_unfolded
        by simp_all
      hence "s_check (v(x := z)) \<alpha> sp'" "s_at sp' = i"
        by auto
      hence "\<exists>sp'. s_at sp' = i \<and> s_check (v(x := z)) \<alpha> sp'"
        using IH_unfolded
        by blast
      hence "\<exists>vp. v_at vp = i \<and> v_check (v(x := z)) (MFOTL.Neg \<alpha>) vp"
        using IH_unfolded
        by blast
    }
    note IH_new = this
    have obs: "\<exists>part. v_at (VExists x part) = i \<and> (\<forall>(sub, vp) \<in> SubsVals part. \<forall>z \<in> sub. v_check (v (x := z)) (formula.Neg \<alpha>) vp)  
    \<Longrightarrow> \<exists>vp. v_at vp = i \<and> local.v_check v (formula.Exists x (formula.Neg \<alpha>)) vp"
      apply clarsimp
      subgoal for part by (auto intro!: exI[of _ "VExists x part"])
      done
    show ?case
      using Neg
      unfolding Neg
      apply clarify
      apply (rule obs)
      using IH_new[of ]
      apply (clarsimp split: prod.splits)
      sorry
  next
    case (Or x61 x62)
    then show ?case sorry
  next
    case (And x71 x72)
    then show ?case sorry
  next
    case (Imp x81 x82)
    then show ?case sorry
  next
    case (Iff x91 x92)
    then show ?case sorry
  next
    case (Exists y \<alpha>)
    then show ?case
      using VExists
      sorry
  next
    case (Forall x111 x112)
    then show ?case sorry
  next
    case (Prev x121 x122)
    then show ?case sorry
  next
    case (Next x131 x132)
    then show ?case sorry
  next
    case (Once x141 x142)
    then show ?case sorry
  next
    case (Historically x151 x152)
    then show ?case sorry
  next
    case (Eventually x161 x162)
    then show ?case sorry
  next
    case (Always x171 x172)
    then show ?case sorry
  next
    case (Since x181 x182 x183)
    then show ?case sorry
  next
    case (Until x191 x192 x193)
    then show ?case sorry
  qed simp
next
  case (SForall v x i \<phi>)
  then show ?case sorry
next
  case (VForall v x i \<phi>)
  then show ?case sorry
next
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
  case (SSince j i I v \<psi> \<phi>)
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
  case (SUntil j i I v \<psi> \<phi>)
  then show ?case sorry
next
  case (VUntil I j i v \<phi> \<psi>)
  then show ?case sorry
next
  case (VUntilInf I i v \<psi> \<phi>)
  then show ?case sorry
qed

definition "p_at = (\<lambda>p. case_sum s_at v_at p)"

definition "p_check_exec = (\<lambda>vs \<phi> p. case_sum (s_check_exec vs \<phi>) (v_check_exec vs \<phi>) p)"

definition valid :: "'d MFOTL.envset \<Rightarrow> nat \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd proof \<Rightarrow> bool" where
  "valid vs i \<phi> p = 
    (case p of
      Inl p \<Rightarrow> s_check_exec vs \<phi> p \<and> s_at p = i
    | Inr p \<Rightarrow> v_check_exec vs \<phi> p \<and> v_at p = i)"

end

section \<open>Algorithm\<close>

definition proof_app :: "'d proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof" (infixl "\<oplus>" 65) where
  "p \<oplus> q = (case (p, q) of
   (Inl (SHistorically i li sps), Inl q) \<Rightarrow> Inl (SHistorically (i+1) li (sps @ [q]))
 | (Inl (SAlways i hi sps), Inl q) \<Rightarrow> Inl (SAlways (i-1) hi (q # sps))
 | (Inl (SSince sp2 sp1s), Inl q) \<Rightarrow> Inl (SSince sp2 (sp1s @ [q]))
 | (Inl (SUntil sp1s sp2), Inl q) \<Rightarrow> Inl (SUntil (q # sp1s) sp2)
 | (Inr (VSince i vp1 vp2s), Inr q) \<Rightarrow> Inr (VSince (i+1) vp1 (vp2s @ [q]))
 | (Inr (VOnce i li vps), Inr q) \<Rightarrow> Inr (VOnce (i+1) li (vps @ [q]))
 | (Inr (VEventually i hi vps), Inr q) \<Rightarrow> Inr (VEventually (i-1) hi (q # vps))
 | (Inr (VSinceInf i li vp2s), Inr q) \<Rightarrow> Inr (VSinceInf (i+1) li (vp2s @ [q]))
 | (Inr (VUntil i vp2s vp1), Inr q) \<Rightarrow> Inr (VUntil (i-1) (q # vp2s) vp1)
 | (Inr (VUntilInf i hi vp2s), Inr q) \<Rightarrow> Inr (VUntilInf (i-1) hi (q # vp2s)))"

definition proof_incr :: "'d proof \<Rightarrow> 'd proof" where
  "proof_incr p = (case p of
   Inl (SOnce i sp) \<Rightarrow> Inl (SOnce (i+1) sp)
 | Inl (SEventually i sp) \<Rightarrow> Inl (SEventually (i-1) sp)
 | Inl (SHistorically i li sps) \<Rightarrow> Inl (SHistorically (i+1) li sps)
 | Inl (SAlways i hi sps) \<Rightarrow> Inl (SAlways (i-1) hi sps)
 | Inr (VSince i vp1 vp2s) \<Rightarrow> Inr (VSince (i+1) vp1 vp2s)
 | Inr (VOnce i li vps) \<Rightarrow> Inr (VOnce (i+1) li vps)
 | Inr (VEventually i hi vps) \<Rightarrow> Inr (VEventually (i-1) hi vps)
 | Inr (VHistorically i vp) \<Rightarrow> Inr (VHistorically (i+1) vp)
 | Inr (VAlways i vp) \<Rightarrow> Inr (VAlways (i-1) vp)
 | Inr (VSinceInf i li vp2s) \<Rightarrow> Inr (VSinceInf (i+1) li vp2s)
 | Inr (VUntil i vp2s vp1) \<Rightarrow> Inr (VUntil (i-1) vp2s vp1)
 | Inr (VUntilInf i hi vp2s) \<Rightarrow> Inr (VUntilInf (i-1) hi vp2s))"

definition min_list_wrt :: "('d proof \<Rightarrow> 'd proof \<Rightarrow> bool) \<Rightarrow> 'd proof list \<Rightarrow> 'd proof" where
  "min_list_wrt r xs = hd [x \<leftarrow> xs. \<forall>y \<in> set xs. r x y]"

definition do_neg :: "'d proof \<Rightarrow> 'd proof list" where
  "do_neg p = (case p of
  Inl sp \<Rightarrow> [Inr (VNeg sp)]
| Inr vp \<Rightarrow> [Inl (SNeg vp)])"

definition do_or :: "'d proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_or p1 p2 = (case (p1, p2) of
  (Inl sp1, Inl sp2) \<Rightarrow> [Inl (SOrL sp1), Inl (SOrR sp2)]
| (Inl sp1, Inr _  ) \<Rightarrow> [Inl (SOrL sp1)]
| (Inr _  , Inl sp2) \<Rightarrow> [Inl (SOrR sp2)]
| (Inr vp1, Inr vp2) \<Rightarrow> [Inr (VOr vp1 vp2)])"

definition do_and :: "'d proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_and p1 p2 = (case (p1, p2) of
  (Inl sp1, Inl sp2) \<Rightarrow> [Inl (SAnd sp1 sp2)]
| (Inl _  , Inr vp2) \<Rightarrow> [Inr (VAndR vp2)]
| (Inr vp1, Inl _  ) \<Rightarrow> [Inr (VAndL vp1)]
| (Inr vp1, Inr vp2) \<Rightarrow> [Inr (VAndL vp1), Inr (VAndR vp2)])"

definition do_imp :: "'d proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_imp p1 p2 = (case (p1, p2) of
  (Inl _  , Inl sp2) \<Rightarrow> [Inl (SImpR sp2)]
| (Inl sp1, Inr vp2) \<Rightarrow> [Inr (VImp sp1 vp2)]
| (Inr vp1, Inl sp2) \<Rightarrow> [Inl (SImpL vp1), Inl (SImpR sp2)]
| (Inr vp1, Inr _  ) \<Rightarrow> [Inl (SImpL vp1)])"

definition do_iff :: "'d proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_iff p1 p2 = (case (p1, p2) of
  (Inl sp1, Inl sp2) \<Rightarrow> [Inl (SIffSS sp1 sp2)]
| (Inl sp1, Inr vp2) \<Rightarrow> [Inr (VIffSV sp1 vp2)]
| (Inr vp1, Inl sp2) \<Rightarrow> [Inr (VIffVS vp1 sp2)]
| (Inr vp1, Inr vp2) \<Rightarrow> [Inl (SIffVV vp1 vp2)])"

definition do_exists :: "MFOTL.name \<Rightarrow> ('d::{default,linorder}) proof + ('d, 'd proof) part \<Rightarrow> 'd proof list" where
  "do_exists x p_part = (case p_part of
  Inl p \<Rightarrow> (case p of
    Inl sp \<Rightarrow> [Inl (SExists x default sp)]
  | Inr vp \<Rightarrow> [Inr (VExists x (trivial_part vp))])
| Inr part \<Rightarrow> (if (\<exists>x\<in>Vals part. isl x) then 
                map (\<lambda>(D,p). map_sum (SExists x (Min D)) id p) (filter (\<lambda>(_, p). isl p) (subsvals part))
              else
                [Inr (VExists x (map_part projr part))]))"

definition do_forall :: "MFOTL.name \<Rightarrow> ('d::{default,linorder}) proof + ('d, 'd proof) part \<Rightarrow> 'd proof list" where
  "do_forall x p_part = (case p_part of
  Inl p \<Rightarrow> (case p of
    Inl sp \<Rightarrow> [Inl (SForall x (trivial_part sp))]
  | Inr vp \<Rightarrow> [Inr (VForall x default vp)])
| Inr part \<Rightarrow> (if (\<forall>x\<in>Vals part. isl x) then 
                [Inl (SForall x (map_part projl part))]
              else 
                map (\<lambda>(D,p). map_sum id (VForall x (Min D)) p) (filter (\<lambda>(_, p). \<not>isl p) (subsvals part))))"

definition do_prev :: "nat \<Rightarrow> \<I> \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_prev i I t p = (case (p, t < left I) of
  (Inl _ , True) \<Rightarrow> [Inr (VPrevOutL i)]
| (Inl sp, False) \<Rightarrow> (if mem t I then [Inl (SPrev sp)] else [Inr (VPrevOutR i)])
| (Inr vp, True) \<Rightarrow> [Inr (VPrev vp), Inr (VPrevOutL i)]
| (Inr vp, False) \<Rightarrow> (if mem t I then [Inr (VPrev vp)] else [Inr (VPrev vp), Inr (VPrevOutR i)]))"

definition do_next :: "nat \<Rightarrow> \<I> \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_next i I t p = (case (p, t < left I) of
  (Inl _ , True) \<Rightarrow> [Inr (VNextOutL i)]
| (Inl sp, False) \<Rightarrow> (if mem t I then [Inl (SNext sp)] else [Inr (VNextOutR i)])
| (Inr vp, True) \<Rightarrow> [Inr (VNext vp), Inr (VNextOutL i)]
| (Inr vp, False) \<Rightarrow> (if mem t I then [Inr (VNext vp)] else [Inr (VNext vp), Inr (VNextOutR i)]))"

definition do_once_base :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_once_base i a p' = (case (p', a = 0) of
  (Inl sp', True) \<Rightarrow> [Inl (SOnce i sp')]
| (Inr vp', True) \<Rightarrow> [Inr (VOnce i i [vp'])]
| ( _ , False) \<Rightarrow> [Inr (VOnce i i [])])"

definition do_once :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_once i a p p' = (case (p, a = 0, p') of
  (Inl sp, True,  Inr _ ) \<Rightarrow> [Inl (SOnce i sp)]
| (Inl sp, True,  Inl (SOnce _ sp')) \<Rightarrow> [Inl (SOnce i sp'), Inl (SOnce i sp)]
| (Inl _ , False, Inl (SOnce _ sp')) \<Rightarrow> [Inl (SOnce i sp')]
| (Inl _ , False, Inr (VOnce _ li vps')) \<Rightarrow> [Inr (VOnce i li vps')]
| (Inr _ , True,  Inl (SOnce _ sp')) \<Rightarrow> [Inl (SOnce i sp')]
| (Inr vp, True,  Inr vp') \<Rightarrow> [(Inr vp') \<oplus> (Inr vp)]
| (Inr _ , False, Inl (SOnce _ sp')) \<Rightarrow> [Inl (SOnce i sp')]
| (Inr _ , False, Inr (VOnce _ li vps')) \<Rightarrow> [Inr (VOnce i li vps')])"

definition do_eventually_base :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_eventually_base i a p' = (case (p', a = 0) of
  (Inl sp', True) \<Rightarrow> [Inl (SEventually i sp')]
| (Inr vp', True) \<Rightarrow> [Inr (VEventually i i [vp'])]
| ( _ , False) \<Rightarrow> [Inr (VEventually i i [])])"

definition do_eventually :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_eventually i a p p' = (case (p, a = 0, p') of
  (Inl sp, True,  Inr _ ) \<Rightarrow> [Inl (SEventually i sp)]
| (Inl sp, True,  Inl (SEventually _ sp')) \<Rightarrow> [Inl (SEventually i sp'), Inl (SEventually i sp)]
| (Inl _ , False, Inl (SEventually _ sp')) \<Rightarrow> [Inl (SEventually i sp')]
| (Inl _ , False, Inr (VEventually _ hi vps')) \<Rightarrow> [Inr (VEventually i hi vps')]
| (Inr _ , True,  Inl (SEventually _ sp')) \<Rightarrow> [Inl (SEventually i sp')]
| (Inr vp, True,  Inr vp') \<Rightarrow> [(Inr vp') \<oplus> (Inr vp)]
| (Inr _ , False, Inl (SEventually _ sp')) \<Rightarrow> [Inl (SEventually i sp')]
| (Inr _ , False, Inr (VEventually _ hi vps')) \<Rightarrow> [Inr (VEventually i hi vps')])"

definition do_historically_base :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_historically_base i a p' = (case (p', a = 0) of
  (Inl sp', True) \<Rightarrow> [Inl (SHistorically i i [sp'])]
| (Inr vp', True) \<Rightarrow> [Inr (VHistorically i vp')]
| ( _ , False) \<Rightarrow> [Inl (SHistorically i i [])])"

definition do_historically :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_historically i a p p' = (case (p, a = 0, p') of
  (Inl _ , True,  Inr (VHistorically _ vp')) \<Rightarrow> [Inr (VHistorically i vp')]
| (Inl sp, True,  Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp)]
| (Inl _ , False, Inl (SHistorically _ li sps')) \<Rightarrow> [Inl (SHistorically i li sps')]
| (Inl _ , False, Inr (VHistorically _ vp')) \<Rightarrow> [Inr (VHistorically i vp')]
| (Inr vp, True,  Inl _ ) \<Rightarrow> [Inr (VHistorically i vp)]
| (Inr vp, True,  Inr (VHistorically _ vp')) \<Rightarrow> [Inr (VHistorically i vp), Inr (VHistorically i vp')]
| (Inr _ , False, Inl (SHistorically _ li sps')) \<Rightarrow> [Inl (SHistorically i li sps')]
| (Inr _ , False, Inr (VHistorically _ vp')) \<Rightarrow> [Inr (VHistorically i vp')])"

definition do_always_base :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_always_base i a p' = (case (p', a = 0) of
  (Inl sp', True) \<Rightarrow> [Inl (SAlways i i [sp'])]
| (Inr vp', True) \<Rightarrow> [Inr (VAlways i vp')]
| ( _ , False) \<Rightarrow> [Inl (SAlways i i [])])"

definition do_always :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_always i a p p' = (case (p, a = 0, p') of
  (Inl _ , True,  Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp')]
| (Inl sp, True,  Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp)]
| (Inl _ , False, Inl (SAlways _ hi sps')) \<Rightarrow> [Inl (SAlways i hi sps')]
| (Inl _ , False, Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp')]
| (Inr vp, True,  Inl _ ) \<Rightarrow> [Inr (VAlways i vp)]
| (Inr vp, True,  Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp), Inr (VAlways i vp')]
| (Inr _ , False, Inl (SAlways _ hi sps')) \<Rightarrow> [Inl (SAlways i hi sps')]
| (Inr _ , False, Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp')])"

definition do_since_base :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_since_base i a p1 p2 = (case (p1, p2, a = 0) of
  ( _ , Inl sp2, True) \<Rightarrow> [Inl (SSince sp2 [])]
| (Inl _ , _ , False) \<Rightarrow> [Inr (VSinceInf i i [])]
| (Inl _ , Inr vp2, True) \<Rightarrow> [Inr (VSinceInf i i [vp2])]
| (Inr vp1, _ , False) \<Rightarrow> [Inr (VSince i vp1 []), Inr (VSinceInf i i [])]
| (Inr vp1, Inr sp2, True) \<Rightarrow> [Inr (VSince i vp1 [sp2]), Inr (VSinceInf i i [sp2])])"

definition do_since :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_since i a p1 p2 p' = (case (p1, p2, a = 0, p') of 
  (Inl sp1, Inr _ , True, Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp1)]
| (Inl sp1, _ , False, Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp1)]
| (Inl sp1, Inl sp2, True, Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp1), Inl (SSince sp2 [])]
| (Inl _ , Inr vp2, True, Inr (VSinceInf _ _ _ )) \<Rightarrow> [p' \<oplus> (Inr vp2)]
| (Inl _ , _ , False, Inr (VSinceInf _ li vp2s')) \<Rightarrow> [Inr (VSinceInf i li vp2s')]
| (Inl _ , Inr vp2, True, Inr (VSince _ _ _ )) \<Rightarrow> [p' \<oplus> (Inr vp2)]
| (Inl _ , _ , False, Inr (VSince _ vp1' vp2s')) \<Rightarrow> [Inr (VSince i vp1' vp2s')]
| (Inr vp1, Inr vp2, True, Inl _ ) \<Rightarrow> [Inr (VSince i vp1 [vp2])]
| (Inr vp1, _ , False, Inl _ ) \<Rightarrow> [Inr (VSince i vp1 [])]
| (Inr _ , Inl sp2, True, Inl _ ) \<Rightarrow> [Inl (SSince sp2 [])]
| (Inr vp1, Inr vp2, True, Inr (VSinceInf _ _ _ )) \<Rightarrow> [Inr (VSince i vp1 [vp2]), p' \<oplus> (Inr vp2)]
| (Inr vp1, _, False, Inr (VSinceInf _ li vp2s')) \<Rightarrow> [Inr (VSince i vp1 []), Inr (VSinceInf i li vp2s')]
| ( _ , Inl sp2, True, Inr (VSinceInf _ _ _ )) \<Rightarrow> [Inl (SSince sp2 [])]
| (Inr vp1, Inr vp2, True, Inr (VSince _ _ _ )) \<Rightarrow> [Inr (VSince i vp1 [vp2]), p' \<oplus> (Inr vp2)]
| (Inr vp1, _ , False, Inr (VSince _ vp1' vp2s')) \<Rightarrow> [Inr (VSince i vp1 []), Inr (VSince i vp1' vp2s')]
| ( _ , Inl vp2, True, Inr (VSince _ _ _ )) \<Rightarrow> [Inl (SSince vp2 [])])"

definition do_until_base :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_until_base i a p1 p2 = (case (p1, p2, a = 0) of
  ( _ , Inl sp2, True) \<Rightarrow> [Inl (SUntil [] sp2)]
| (Inl sp1, _ , False) \<Rightarrow> [Inr (VUntilInf i i [])]
| (Inl sp1, Inr vp2, True) \<Rightarrow> [Inr (VUntilInf i i [vp2])]
| (Inr vp1, _ , False) \<Rightarrow> [Inr (VUntil i [] vp1), Inr (VUntilInf i i [])]
| (Inr vp1, Inr vp2, True) \<Rightarrow> [Inr (VUntil i [vp2] vp1), Inr (VUntilInf i i [vp2])])"

definition do_until :: "nat \<Rightarrow> nat \<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof)
\<Rightarrow> ('a sproof + 'a vproof) \<Rightarrow> ('a sproof + 'a vproof) list" where
  "do_until i a p1 p2 p' = (case (p1, p2, a = 0, p') of
  (Inl sp1, Inr _ , True, Inl (SUntil _ _ )) \<Rightarrow> [p' \<oplus> (Inl sp1)]
| (Inl sp1, _ , False, Inl (SUntil _ _ )) \<Rightarrow> [p' \<oplus> (Inl sp1)]
| (Inl sp1, Inl sp2, True, Inl (SUntil _ _ )) \<Rightarrow> [p' \<oplus> (Inl sp1), Inl (SUntil [] sp2)]
| (Inl _ , Inr vp2, True, Inr (VUntilInf _ _ _ )) \<Rightarrow> [p' \<oplus> (Inr vp2)]
| (Inl _ , _ , False, Inr (VUntilInf _ hi vp2s')) \<Rightarrow> [Inr (VUntilInf i hi vp2s')]
| (Inl _ , Inr vp2, True, Inr (VUntil _ _ _ )) \<Rightarrow> [p' \<oplus> (Inr vp2)]
| (Inl _ , _ , False, Inr (VUntil _ vp2s' vp1')) \<Rightarrow> [Inr (VUntil i vp2s' vp1')]
| (Inr vp1, Inr vp2, True, Inl (SUntil _ _ )) \<Rightarrow> [Inr (VUntil i [vp2] vp1)]
| (Inr vp1, _ , False, Inl (SUntil _ _ )) \<Rightarrow> [Inr (VUntil i [] vp1)]
| (Inr vp1, Inl sp2, True, Inl (SUntil _ _ )) \<Rightarrow> [Inl (SUntil [] sp2)]
| (Inr vp1, Inr vp2, True, Inr (VUntilInf _ _ _ )) \<Rightarrow> [Inr (VUntil i [vp2] vp1), p' \<oplus> (Inr vp2)]
| (Inr vp1, _ , False, Inr (VUntilInf _ hi vp2s')) \<Rightarrow> [Inr (VUntil i [] vp1), Inr (VUntilInf i hi vp2s')]
| ( _ , Inl sp2, True, Inr (VUntilInf _ hi vp2s')) \<Rightarrow> [Inl (SUntil [] sp2)]
| (Inr vp1, Inr vp2, True, Inr (VUntil _ _ _ )) \<Rightarrow> [Inr (VUntil i [vp2] vp1), p' \<oplus> (Inr vp2)]
| (Inr vp1, _ , False, Inr (VUntil _ vp2s' vp1')) \<Rightarrow> [Inr (VUntil i [] vp1), Inr (VUntil i vp2s' vp1')]
| ( _ , Inl sp2, True, Inr (VUntil _ _ _ )) \<Rightarrow> [Inl (SUntil [] sp2)])"

context 
  fixes \<sigma> :: "'d :: {default, linorder} MFOTL.trace" and
  cmp :: "'d proof \<Rightarrow> 'd proof \<Rightarrow> bool"
begin

definition optimal :: "'d MFOTL.envset \<Rightarrow> nat \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd proof \<Rightarrow> bool" where
  "optimal vs i \<phi> p = (valid \<sigma> vs i \<phi> p \<and> (\<forall>q. valid \<sigma> vs i \<phi> q \<longrightarrow> cmp p q))"

fun match :: "'d MFOTL.trm list \<Rightarrow> 'd list \<Rightarrow> (MFOTL.name \<rightharpoonup> 'd) option" where
  "match [] [] = Some Map.empty"
| "match (MFOTL.Const x # ts) (y # ys) = (if x = y then match ts ys else None)"
| "match (MFOTL.Var x # ts) (y # ys) = (case match ts ys of
      None \<Rightarrow> None
    | Some f \<Rightarrow> (case f x of
        None \<Rightarrow> Some (f(x \<mapsto> y))
      | Some z \<Rightarrow> if y = z then Some f else None))"
| "match _ _ = None"

lift_definition tabulate :: "'d list \<Rightarrow> ('d \<Rightarrow> 'v) \<Rightarrow> 'v \<Rightarrow> ('d, 'v) part" is
  "\<lambda>ds f z. (- set ds, z) # map (\<lambda>d. ({d}, f d)) ds"
  sorry

(* Note: this is only used in the Pred case.                                    *)
(* Based on a set of (partial) functions from variables to values of a domain,  *)
(* we compute values for each one of the variables in vars, put them in a list, *)
(* and we create a partition with subsets considering each one of these values  *)
(* and another subset considering the complement of the union of these values.  *)
fun pdt_of :: "nat \<Rightarrow> MFOTL.name \<Rightarrow> 'd MFOTL.trm list \<Rightarrow> MFOTL.name list \<Rightarrow> (MFOTL.name \<rightharpoonup> 'd) set \<Rightarrow> 'd expl" where
  "pdt_of i r ts [] V = (if V = {} then Leaf (Inr (VPred i r ts)) else Leaf (Inl (SPred i r ts)))"
| "pdt_of i r ts (x # vars) V =
     (let ds = sorted_list_of_set (Option.these {v x | v. v \<in> V});
          part = tabulate ds (\<lambda>d. pdt_of i r ts vars ({v \<in> V. v x = Some d})) (pdt_of i r ts vars {})
     in Node x part)"

(* value "pdt_of 0 p [MFOTL.Var ''x'', MFOTL.Var ''y''] [''x'', ''y''] {}" *)

fun "apply_pdt2" :: "MFOTL.name list \<Rightarrow> ('d proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof) \<Rightarrow> 'd expl \<Rightarrow> 'd expl \<Rightarrow> 'd expl" where
  "apply_pdt2 vars f (Leaf pt1) (Leaf pt2) = Leaf (f pt1 pt2)"
| "apply_pdt2 vars f (Leaf pt1) (Node x part2) = Node x (map_part (map_pdt (f pt1)) part2)"
| "apply_pdt2 vars f (Node x part1) (Leaf pt2) = Node x (map_part (map_pdt (\<lambda>pt1. f pt1 pt2)) part1)"
| "apply_pdt2 (z # vars) f (Node x part1) (Node y part2) =
    (if x = z \<and> y = z then
      Node z (merge_part (apply_pdt2 vars f) part1 part2)
    else if x = z then
      Node x (map_part (\<lambda>expl1. apply_pdt2 vars f expl1 (Node y part2)) part1)
    else if y = z then
      Node y (map_part (\<lambda>expl2. apply_pdt2 vars f (Node x part1) expl2) part2)
    else
      apply_pdt2 vars f (Node x part1) (Node y part2))"
| "apply_pdt2 [] _ (Node _ _) (Node _ _) = undefined"

fun "apply_pdt1" :: "MFOTL.name list \<Rightarrow> ('d proof \<Rightarrow> 'd proof) \<Rightarrow> 'd expl \<Rightarrow> 'd expl" where
  "apply_pdt1 vars f (Leaf pt) = Leaf (f pt)"
| "apply_pdt1 (z # vars) f (Node x part) =
    (if x = z then
      Node x (map_part (\<lambda>expl. apply_pdt1 vars f expl) part)
    else
      apply_pdt1 vars f (Node x part))"
| "apply_pdt1 [] _ (Node _ _) = undefined"

fun "hide_pdt" :: "MFOTL.name list \<Rightarrow> ('d proof + ('d, 'd proof) part \<Rightarrow> 'd proof) \<Rightarrow> 'd expl \<Rightarrow> 'd expl" where
  "hide_pdt vars f (Leaf pt) = Leaf (f (Inl pt))"
| "hide_pdt [x] f (Node y part) = Leaf (f (Inr (map_part unleaf part)))"
| "hide_pdt (x # xs) f (Node y part) = 
  (if x = y then
     Node y (map_part (hide_pdt xs f) part)
   else
     hide_pdt xs f (Node y part))"
| "hide_pdt [] _ _ = undefined"

inductive sat_vorder :: "MFOTL.name list \<Rightarrow> 'd expl \<Rightarrow> bool" where
  "sat_vorder vars (Leaf _)"
| "\<forall>expl \<in> Vals part1. sat_vorder vars expl \<Longrightarrow> sat_vorder (x # vars) (Node x part1)"
| "sat_vorder vars (Node x part1) \<Longrightarrow> x \<noteq> z \<Longrightarrow> sat_vorder (z # vars) (Node x part1)"

function (sequential) opt :: "MFOTL.name list \<Rightarrow> nat \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd expl" where
  "opt vars i MFOTL.TT = Leaf (Inl (STT i))"
| "opt vars i MFOTL.FF = Leaf (Inr (VFF i))"
| "opt vars i (MFOTL.Pred r ts) = 
  (pdt_of i r ts vars (Option.these (match ts ` snd ` {rd \<in> \<Gamma> \<sigma> i. fst rd = r })))"
| "opt vars i (MFOTL.Neg \<phi>) = apply_pdt1 vars (\<lambda>p. min_list_wrt cmp (do_neg p)) (opt vars i \<phi>)"
| "opt vars i (MFOTL.Or \<phi> \<psi>) = apply_pdt2 vars (\<lambda>p1 p2. min_list_wrt cmp (do_or p1 p2)) (opt vars i \<phi>) (opt vars i \<psi>)"
| "opt vars i (MFOTL.And \<phi> \<psi>) = apply_pdt2 vars (\<lambda>p1 p2. min_list_wrt cmp (do_and p1 p2)) (opt vars i \<phi>) (opt vars i \<psi>)"
| "opt vars i (MFOTL.Imp \<phi> \<psi>) = apply_pdt2 vars (\<lambda>p1 p2. min_list_wrt cmp (do_imp p1 p2)) (opt vars i \<phi>) (opt vars i \<psi>)"
| "opt vars i (MFOTL.Iff \<phi> \<psi>) = apply_pdt2 vars (\<lambda>p1 p2. min_list_wrt cmp (do_iff p1 p2)) (opt vars i \<phi>) (opt vars i \<psi>)"
| "opt vars i (MFOTL.Exists x \<phi>) = hide_pdt (vars @ [x]) (\<lambda>p. min_list_wrt cmp (do_exists x p)) (opt (vars @ [x]) i \<phi>)"
| "opt vars i (MFOTL.Forall x \<phi>) = hide_pdt (vars @ [x]) (\<lambda>p. min_list_wrt cmp (do_forall x p)) (opt (vars @ [x]) i \<phi>)"
| "opt vars i (MFOTL.Prev I \<phi>) = (if i = 0 then Leaf (Inr VPrevZ) 
                                  else apply_pdt1 vars (\<lambda>p. min_list_wrt cmp (do_prev i I (\<Delta> \<sigma> i) p)) (opt vars (i-1) \<phi>))"
| "opt vars i (MFOTL.Next I \<phi>) = apply_pdt1 vars (\<lambda>l. min_list_wrt cmp (do_next i I (\<Delta> \<sigma> (i+1)) l)) (opt vars (i+1) \<phi>)"
| "opt vars i (MFOTL.Once I \<phi>) = (if \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I then Leaf (Inr (VOnceOut i)) 
                                  else (let expl' = opt vars i \<phi> in
                                       (if i = 0 then 
                                          apply_pdt1 vars (\<lambda>p. min_list_wrt cmp (do_once_base 0 0 p)) expl'
                                        else (if right I \<ge> enat (\<Delta> \<sigma> i) then
                                                apply_pdt2 vars (\<lambda>p p'. min_list_wrt cmp (do_once i (left I) p p')) expl'
                                                           (opt vars (i-1) (MFOTL.Once (subtract (\<Delta> \<sigma> i) I) \<phi>))
                                              else apply_pdt1 vars (\<lambda>p. min_list_wrt cmp (do_once_base i (left I) p)) expl'))))"
  by pat_completeness auto
termination
  sorry

end

end