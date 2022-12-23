(*<*)
theory Monitor
  imports Proof_System "HOL-Library.Simps_Case_Conv"
begin
(*>*)

lift_definition part_hd :: "('d, 'a) part \<Rightarrow> 'a" is "snd \<circ> hd" .

find_theorems name:sum_list

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
| "s_at (SEq i _ _) = i"
| "s_at (SNeg vp) = v_at vp"
| "s_at (SOrL sp1) = s_at sp1"
| "s_at (SOrR sp2) = s_at sp2"
| "s_at (SAnd sp1 _) = s_at sp1"
| "s_at (SImpL vp1) = v_at vp1"
| "s_at (SImpR sp2) = s_at sp2"
| "s_at (SIffSS sp1 _) = s_at sp1"
| "s_at (SIffVV vp1 _) = v_at vp1"
| "s_at (SExists _ sp) = s_at sp"
| "s_at (SForall part) = s_at (part_hd part)"
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
| "v_at (VEq i _ _ ) = i"
| "v_at (VNeg sp) = s_at sp"
| "v_at (VOr vp1 _) = v_at vp1"
| "v_at (VAndL vp1) = v_at vp1"
| "v_at (VAndR vp2) = v_at vp2"
| "v_at (VImp sp1 _) = s_at sp1"
| "v_at (VIffSV sp1 _) = s_at sp1"
| "v_at (VIffVS vp1 _) = v_at vp1"
| "v_at (VExists part) = v_at (part_hd part)"
| "v_at (VForall _ vp1) = v_at vp1"
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

term set_Cons

value "{''r''} \<times> (listset [{0::nat}, {2,0}, {1,0}])"

fun s_check :: "'d MFOTL.envset \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd sproof \<Rightarrow> bool"
  and v_check :: "'d MFOTL.envset \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd vproof \<Rightarrow> bool" where
  "s_check vs f p = (case (f, p) of
    (MFOTL.TT, STT i) \<Rightarrow> True
  | (MFOTL.Pred r ts, SPred i s ts') \<Rightarrow> 
    (r = s \<and> ts = ts' \<and> {r} \<times> listset (MFOTL.eval_trms_set vs ts) \<subseteq> \<Gamma> \<sigma> i)
  | (MFOTL.Eq t1 t2, SEq i t1' t2') \<Rightarrow> 
    (t1 = t1' \<and> t2 = t2' \<and> (MFOTL.eval_trm_set vs t1) = (MFOTL.eval_trm_set vs t2))
  | (MFOTL.Neg \<phi>, SNeg vp) \<Rightarrow> v_check vs \<phi> vp
  | (MFOTL.Or \<phi> \<psi>, SOrL sp1) \<Rightarrow> s_check vs \<phi> sp1
  | (MFOTL.Or \<phi> \<psi>, SOrR sp2) \<Rightarrow> s_check vs \<psi> sp2
  | (MFOTL.And \<phi> \<psi>, SAnd sp1 sp2) \<Rightarrow> s_check vs \<phi> sp1 \<and> s_check vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (MFOTL.Imp \<phi> \<psi>, SImpL vp1) \<Rightarrow> v_check vs \<phi> vp1
  | (MFOTL.Imp \<phi> \<psi>, SImpR sp2) \<Rightarrow> s_check vs \<psi> sp2
  | (MFOTL.Iff \<phi> \<psi>, SIffSS sp1 sp2) \<Rightarrow> s_check vs \<phi> sp1 \<and> s_check vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (MFOTL.Iff \<phi> \<psi>, SIffVV vp1 vp2) \<Rightarrow> v_check vs \<phi> vp1 \<and> v_check vs \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (MFOTL.Exists x \<phi>, SExists val sp) \<Rightarrow> s_check (vs (x := {val})) \<phi> sp
  | (MFOTL.Forall x \<phi>, SForall sp_part) \<Rightarrow> \<forall>(sub, sp) \<in> SubsVals sp_part. s_check (vs (x := sub)) \<phi> sp
  | (MFOTL.Prev \<I> \<phi>, SPrev sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SPrev sp) in 
    i = j+1 \<and> mem (\<Delta> \<sigma> i) \<I> \<and> s_check vs \<phi> sp)
  | (MFOTL.Next \<I> \<phi>, SNext sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SNext sp) in
    j = i+1 \<and> mem (\<Delta> \<sigma> j) \<I> \<and> s_check vs \<phi> sp)
  | (MFOTL.Once \<I> \<phi>, SOnce i sp) \<Rightarrow> 
    (let j = s_at sp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) \<I> \<and> s_check vs \<phi> sp)
  | (MFOTL.Eventually \<I> \<phi>, SEventually i sp) \<Rightarrow> 
    (let j = s_at sp in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) \<I> \<and> s_check vs \<phi> sp)
  | (MFOTL.Historically \<I> \<phi>, SHistoricallyOut i) \<Rightarrow> 
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left \<I>
  | (MFOTL.Historically \<I> \<phi>, SHistorically i li sps) \<Rightarrow>
    (li = (case right \<I> of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - b))
    \<and> \<tau> \<sigma> 0 + left \<I> \<le> \<tau> \<sigma> i
    \<and> map s_at sps = [li ..< (LTP_p \<sigma> i \<I>) + 1]
    \<and> (\<forall>sp \<in> set sps. s_check vs \<phi> sp))
  | (MFOTL.Always \<I> \<phi>, SAlways i hi sps) \<Rightarrow>
    (hi = (case right \<I> of enat b \<Rightarrow> LTP_f \<sigma> i b) 
    \<and> right \<I> \<noteq> \<infinity>
    \<and> map s_at sps = [(ETP_f \<sigma> i \<I>) ..< hi + 1]
    \<and> (\<forall>sp \<in> set sps. s_check vs \<phi> sp))
  | (MFOTL.Since \<phi> \<I> \<psi>, SSince sp2 sp1s) \<Rightarrow>
    (let i = s_at (SSince sp2 sp1s); j = s_at sp2 in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) \<I> 
    \<and> map s_at sp1s = [j+1 ..< i+1] 
    \<and> s_check vs \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check vs \<phi> sp1))
  | (MFOTL.Until \<phi> \<I> \<psi>, SUntil sp1s sp2) \<Rightarrow>
    (let i = s_at (SUntil sp1s sp2); j = s_at sp2 in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) \<I>
    \<and> map s_at sp1s = [i ..< j] \<and> s_check vs \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check vs \<phi> sp1))
  | (_, _) \<Rightarrow> False)"
| "v_check vs f p = (case (f, p) of
    (MFOTL.FF, VFF i) \<Rightarrow> True
  | (MFOTL.Pred r ts, VPred i pred ts') \<Rightarrow> 
    (r = pred \<and> ts = ts' \<and> {r} \<times> listset (map (MFOTL.eval_trm_set vs) ts) \<subseteq> - \<Gamma> \<sigma> i)
  | (MFOTL.Eq t1 t2, VEq i t1' t2') \<Rightarrow> 
    (t1 = t1' \<and> t2 = t2' \<and> (MFOTL.eval_trm_set vs t1) \<noteq> (MFOTL.eval_trm_set vs t2))
  | (MFOTL.Neg \<phi>, VNeg sp) \<Rightarrow> s_check vs \<phi> sp
  | (MFOTL.Or \<phi> \<psi>, VOr vp1 vp2) \<Rightarrow> v_check vs \<phi> vp1 \<and> v_check vs \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (MFOTL.And \<phi> \<psi>, VAndL vp1) \<Rightarrow> v_check vs \<phi> vp1
  | (MFOTL.And \<phi> \<psi>, VAndR vp2) \<Rightarrow> v_check vs \<psi> vp2
  | (MFOTL.Imp \<phi> \<psi>, VImp sp1 vp2) \<Rightarrow> s_check vs \<phi> sp1 \<and> v_check vs \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (MFOTL.Iff \<phi> \<psi>, VIffSV sp1 vp2) \<Rightarrow> s_check vs \<phi> sp1 \<and> v_check vs \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (MFOTL.Iff \<phi> \<psi>, VIffVS vp1 sp2) \<Rightarrow> v_check vs \<phi> vp1 \<and> s_check vs \<psi> sp2 \<and> v_at vp1 = s_at sp2
  | (MFOTL.Exists x \<phi>, VExists vp_part) \<Rightarrow> \<forall>(sub, vp) \<in> SubsVals vp_part. v_check (vs (x := sub)) \<phi> vp
  | (MFOTL.Forall x \<phi>, VForall val vp) \<Rightarrow> v_check (vs (x := {val})) \<phi> vp
  | (MFOTL.Prev \<I> \<phi>, VPrev vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VPrev vp) in
    i = j+1 \<and> v_check vs \<phi> vp)
  | (MFOTL.Prev \<I> \<phi>, VPrevZ) \<Rightarrow>
    v_at (VPrevZ::'d vproof) = 0
  | (MFOTL.Prev \<I> \<phi>, VPrevOutL i) \<Rightarrow>
    i > 0 \<and> \<Delta> \<sigma> i < left \<I>
  | (MFOTL.Prev \<I> \<phi>, VPrevOutR i) \<Rightarrow>
    i > 0 \<and> enat (\<Delta> \<sigma> i) > right \<I>
  | (MFOTL.Next \<I> \<phi>, VNext vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VNext vp) in
    j = i+1 \<and> v_check vs \<phi> vp)
  | (MFOTL.Next \<I> \<phi>, VNextOutL i) \<Rightarrow>
    \<Delta> \<sigma> (i+1) < left \<I>
  | (MFOTL.Next \<I> \<phi>, VNextOutR i) \<Rightarrow>
    enat (\<Delta> \<sigma> (i+1)) > right \<I>
  | (MFOTL.Once \<I> \<phi>, VOnceOut i) \<Rightarrow> 
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left \<I>
  | (MFOTL.Once \<I> \<phi>, VOnce i li vps) \<Rightarrow>
    (li = (case right \<I> of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left \<I> \<le> \<tau> \<sigma> i
    \<and> map v_at vps = [li ..< (LTP_p \<sigma> i \<I>) + 1]
    \<and> (\<forall>vp \<in> set vps. v_check vs \<phi> vp))
  | (MFOTL.Eventually \<I> \<phi>, VEventually i hi vps) \<Rightarrow>
    (hi = (case right \<I> of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right \<I> \<noteq> \<infinity>
    \<and> map v_at vps = [(ETP_f \<sigma> i \<I>) ..< hi + 1]
    \<and> (\<forall>vp \<in> set vps. v_check vs \<phi> vp))
  | (MFOTL.Historically \<I> \<phi>, VHistorically i vp) \<Rightarrow> 
    (let j = v_at vp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) \<I> \<and> v_check vs \<phi> vp)
  | (MFOTL.Always \<I> \<phi>, VAlways i vp) \<Rightarrow> 
    (let j = v_at vp
    in j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) \<I> \<and> v_check vs \<phi> vp)
  | (MFOTL.Since \<phi> \<I> \<psi>, VSinceOut i) \<Rightarrow>
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left \<I>
  | (MFOTL.Since \<phi> \<I> \<psi>, VSince i vp1 vp2s) \<Rightarrow>
    (let j = v_at vp1 in
    (case right \<I> of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> ETP_p \<sigma> i b \<le> j) \<and> j \<le> i
    \<and> \<tau> \<sigma> 0 + left \<I> \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [j ..< (LTP_p \<sigma> i \<I>) + 1] \<and> v_check vs \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check vs \<psi> vp2))
  | (MFOTL.Since \<phi> \<I> \<psi>, VSinceInf i li vp2s) \<Rightarrow>
    (li = (case right \<I> of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left \<I> \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [li ..< (LTP_p \<sigma> i \<I>) + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check vs \<psi> vp2))
  | (MFOTL.Until \<phi> \<I> \<psi>, VUntil i vp2s vp1) \<Rightarrow>
    (let j = v_at vp1 in
    (case right \<I> of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> j \<le> LTP_f \<sigma> i b) \<and> i \<le> j
    \<and> map v_at vp2s = [ETP_f \<sigma> i \<I> ..< j + 1] \<and> v_check vs \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check vs \<psi> vp2))
  | (MFOTL.Until \<phi> \<I> \<psi>, VUntilInf i hi vp2s) \<Rightarrow>
    (hi = (case right \<I> of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right \<I> \<noteq> \<infinity>
    \<and> map v_at vp2s = [ETP_f \<sigma> i \<I> ..< hi + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check vs \<psi> vp2))
  | (_, _) \<Rightarrow> False)"

declare s_check.simps[simp del] v_check.simps[simp del]
simps_of_case s_check_simps[simp, code]: s_check.simps[unfolded prod.case] (splits: MFOTL.formula.split sproof.split)
simps_of_case v_check_simps[simp, code]: v_check.simps[unfolded prod.case] (splits: MFOTL.formula.split vproof.split)

lemma check_soundness:
  "s_check vs \<phi> sp \<Longrightarrow> (\<And>x. x \<in> MFOTL.fv \<phi> \<Longrightarrow> v x \<in> vs x) \<Longrightarrow> SAT \<sigma> v (s_at sp) \<phi>"
  "v_check vs \<phi> vp \<Longrightarrow> (\<And>x. x \<in> MFOTL.fv \<phi> \<Longrightarrow> v x \<in> vs x) \<Longrightarrow> VIO \<sigma> v (v_at vp) \<phi>"
  oops

lemma check_completeness:
  assumes "MFOTL.future_bounded \<phi>"
  shows "(SAT \<sigma> v i \<phi> \<longrightarrow> (\<exists>sp. s_at sp = i \<and> s_check vs \<phi> sp)) \<and>
         (VIO \<sigma> v i \<phi> \<longrightarrow> (\<exists>vp. v_at vp = i \<and> v_check vs \<phi> vp))"
  oops

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

consts do_exists :: "'d proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list"

consts do_forall :: "'d proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list"

definition do_prev :: "nat \<Rightarrow> \<I> \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_prev i \<I> ts p = (case (p, ts < left \<I>) of
  (Inl _ , True) \<Rightarrow> [Inr (VPrevOutL i)]
| (Inl sp, False) \<Rightarrow> (if mem ts \<I> then [Inl (SPrev sp)] else [Inr (VPrevOutR i)])
| (Inr vp, True) \<Rightarrow> [Inr (VPrev vp), Inr (VPrevOutL i)]
| (Inr vp, False) \<Rightarrow> (if mem ts \<I> then [Inr (VPrev vp)] else [Inr (VPrev vp), Inr (VPrevOutR i)]))"

definition do_next :: "nat \<Rightarrow> \<I> \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_next i \<I> ts p = (case (p, ts < left \<I>) of
  (Inl _ , True) \<Rightarrow> [Inr (VNextOutL i)]
| (Inl sp, False) \<Rightarrow> (if mem ts \<I> then [Inl (SNext sp)] else [Inr (VNextOutR i)])
| (Inr vp, True) \<Rightarrow> [Inr (VNext vp), Inr (VNextOutL i)]
| (Inr vp, False) \<Rightarrow> (if mem ts \<I> then [Inr (VNext vp)] else [Inr (VNext vp), Inr (VNextOutR i)]))"

definition do_once_base :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_once_base i a p' = (case (p', a = 0) of
  (Inl sp', True) \<Rightarrow> [Inl (SOnce i sp')]
| (Inr vp', True) \<Rightarrow> [Inr (VOnce i i [vp'])]
| (_, False) \<Rightarrow> [Inr (VOnce i i [])])"

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
| (_, False) \<Rightarrow> [Inr (VEventually i i [])])"

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
| (_, False) \<Rightarrow> [Inl (SHistorically i i [])])"

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
| (_, False) \<Rightarrow> [Inl (SAlways i i [])])"

definition do_always :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_always i a p p' = (case (p, a = 0, p') of
  (Inl _ , True,  Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp')]
| (Inl sp, True,  Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp)]
| (Inl _ , False, Inl (SAlways _ li sps')) \<Rightarrow> [Inl (SAlways i li sps')]
| (Inl _ , False, Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp')]
| (Inr vp, True,  Inl _ ) \<Rightarrow> [Inr (VAlways i vp)]
| (Inr vp, True,  Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp), Inr (VAlways i vp')]
| (Inr _ , False, Inl (SAlways _ li sps')) \<Rightarrow> [Inl (SAlways i li sps')]
| (Inr _ , False, Inr (VAlways _ vp')) \<Rightarrow> [Inr (VAlways i vp')])"

definition do_since_base :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_since_base i a p1 p2 = (case (p1, p2, a = 0) of
  ( _ , Inl sp2, True) \<Rightarrow> [Inl (SSince sp2 [])]
| (Inl _ , _ , False) \<Rightarrow> [Inr (VSinceInf i i [])]
| (Inl _ , Inr vp2, True) \<Rightarrow> [Inr (VSinceInf i i [vp2])]
| (Inr vp1, _ , False) \<Rightarrow> [Inr (VSince i vp1 []), Inr (VSinceInf i i [])]
| (Inr vp1, Inr sp2, True) \<Rightarrow> [Inr (VSince i vp1 [sp2]), Inr (VSinceInf i i [sp2])])"

(* definition do_since :: "nat \<Rightarrow> nat \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof \<Rightarrow> 'd proof list" where
  "do_since i a p1 p2 p' = (case (p1, p2, a = 0, p') of
  (Inr vp1, Inr vp2, True, Inl p') \<Rightarrow> [Inr (VSince i vp1 [vp2])]
| (Inr vp1, _ , False, Inl _ ) \<Rightarrow> [Inr (VSince i vp1 [])]
| (Inr _ , Inl sp2, True, Inl _ ) \<Rightarrow> [Inl (SSince sp2 [])]
| (Inl sp1, Inr _ , True, Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp1)]
| (Inl sp1, _ , False, Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp1)]
| (Inl sp1, Inl sp2, True, Inl sp') \<Rightarrow> [(Inl sp') \<oplus> (Inl sp1), Inl (SSince sp2 [])]
| (Inr vp1, Inr vp2, True, Inr (VSinceInf _ _ _ )) \<Rightarrow> [Inr (VSince i vp1 [vp2]), p' \<oplus> (Inr vp2)]
| (Inr vp1, _, False, Inr (VSinceInf _ li vp2s')) \<Rightarrow> [Inr (VSince i vp1 []), Inr (VSinceInf i li vp2s')]
| (_ , Inl sp2, True, Inr (VSinceInf _ _ _ )) \<Rightarrow> [Inl (SSince sp2 [])]
| (Inl _ , Inr vp2, True, Inr (VSinceInf _ _ _ )) \<Rightarrow> [p' \<oplus> (Inr vp2)]
| (Inl _ , _ , False, Inr (VSinceInf _ li vp2s')) \<Rightarrow> [Inr (VSinceInf i li vp2s')]
| (Inr vp1, Inr vp2, True, Inr (VSince _ q1 q2)) \<Rightarrow> [Inr (VSince i p1 [p2]), p' \<oplus> (Inr p2)]
| (Inr p1, _, False, Inr (VSince j q1 q2)) \<Rightarrow> [Inr (VSince i p1 []), Inr (VSince i q1 q2)]
| (_, Inl p2, True, Inr (VSince j q1 q2)) \<Rightarrow> [Inl (SSince p2 [])]
| (Inl p1, Inr p2, True, Inr (VSince j q1 q2)) \<Rightarrow> [p' \<oplus> (Inr p2)]
| (Inl p1, _, False, Inr (VSince j q1 q2)) \<Rightarrow> [Inr (VSince i q1 q2)])" *)


locale alg = 
  fixes \<sigma> :: "'d :: linorder MFOTL.trace" and
  wqo :: "'d proof \<Rightarrow> 'd proof \<Rightarrow> bool"
begin

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

fun pdt_of :: "nat \<Rightarrow> MFOTL.name \<Rightarrow> 'd MFOTL.trm list  \<Rightarrow> MFOTL.name list \<Rightarrow> (MFOTL.name \<rightharpoonup> 'd) set \<Rightarrow> 'd expl" where
  "pdt_of i r ts [] V = (if V = {} then Leaf (Inr (VPred i r ts)) else Leaf (Inl (SPred i r ts)))"
| "pdt_of i r ts (x # vars) V =
     (let ds = sorted_list_of_set (Option.these {v x | v. v \<in> V});
          part = tabulate ds (\<lambda>d. pdt_of i r ts vars ({v \<in> V. v x = Some d})) (pdt_of i r ts vars {})
     in Node x part)"

function (sequential) opt :: "MFOTL.name list \<Rightarrow> nat \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd expl" where
  "opt vars i MFOTL.TT = Leaf (Inl (STT i))"
| "opt vars i MFOTL.FF = Leaf (Inr (VFF i))"
| "opt vars i (MFOTL.Pred r ts) = 
  (pdt_of i r ts vars (Option.these (match ts ` {d. (r, d) \<in> \<Gamma> \<sigma> i})))"
| "opt vars i (MFOTL.Or \<phi> \<psi>) = apply_pdt vars (\<lambda>l r. min_list_wrt wqo (do_or l r)) (opt vars i \<phi>) (opt vars i \<psi>)"
(*| "opt vars vs i (MFOTL.And \<phi> \<psi>) = apply_pdt vars do_and (opt vars vs i \<phi>) (opt vars vs i \<psi>)"
| "opt vars vs i (MFOTL.Imp \<phi> \<psi>) = apply_pdt vars do_imp (opt vars vs i \<phi>) (opt vars vs i \<psi>)"
| "opt vars vs i (MFOTL.Iff \<phi> \<psi>) = apply_pdt vars do_iff (opt vars vs i \<phi>) (opt vars vs i \<psi>)"*)
  by pat_completeness auto

end

end