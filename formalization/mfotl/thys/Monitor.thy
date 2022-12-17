(*<*)
theory Monitor
  imports Proof_System
begin
(*>*)

lift_definition part_hd :: "('d, 'a) part \<Rightarrow> 'a" is "snd \<circ> hd" .

lemma part_hd_Vals[termination_simp]: "part_hd part \<in> Vals part"
  apply transfer
   apply auto
  oops

lemma part_hd_SForall_estimation[termination_simp]: "size (part_hd part) < size (SForall part)"
  oops

lemma size_last_estimation[termination_simp]: "xs \<noteq> [] \<Longrightarrow> size (last xs) < size_list size xs"
  by (induct xs) auto

(* fun s_at'' :: "'d sproof \<Rightarrow> nat" where
  "s_at'' (STT i) = i"
| "s_at'' (SForall part) = s_at'' (part_hd part)" *)

(* function (sequential) s_at' :: "'d sproof \<Rightarrow> nat" where
  "s_at' (STT i) = i"
| "s_at' (SForall part) = s_at' (part_hd part)"
  by pat_completeness auto
termination
  apply(relation "measure f")
   apply simp_all *)

function (sequential) s_at :: "'d sproof \<Rightarrow> nat" and 
  v_at :: "'d vproof \<Rightarrow> nat" where
  "s_at (STT i) = i"
| "s_at (SPred i _ _) = i"
| "s_at (SEq i _ _) = i"
| "s_at (SNeg vp) = v_at vp"
| "s_at (SOrL sp1) = s_at sp1"
| "s_at (SOrR sp2) = s_at sp2"
| "s_at (SAnd sp1 _) = s_at sp1"
| "s_at (SImplL vp1) = v_at vp1"
| "s_at (SImplR sp2) = s_at sp2"
| "s_at (SIffSS sp1 _) = s_at sp1"
| "s_at (SIffVV vp1 _) = v_at vp1"
| "s_at (SExists sp) = s_at sp"
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
| "v_at (VImpl sp1 _) = s_at sp1"
| "v_at (VIffSV sp1 _) = s_at sp1"
| "v_at (VIffVS vp1 _) = v_at vp1"
| "v_at (VExists part) = v_at (part_hd part)"
| "v_at (VForall vp1) = v_at vp1"
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
  by pat_completeness auto
termination
  sorry

context fixes \<sigma> :: "'a MFOTL.trace"

begin

primrec eval_trm_set :: "'a MFOTL.envset \<Rightarrow> 'a MFOTL.trm \<Rightarrow> 'a set" where
  "eval_trm_set vs (MFOTL.Var x) = vs x"
| "eval_trm_set vs (MFOTL.Const x) = {x}"

value "{5::nat} \<times> listset[{1::nat, 2}, {2::nat, 3}]"

fun s_check :: "'a MFOTL.envset \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a sproof \<Rightarrow> bool"
  and v_check :: "'a MFOTL.envset \<Rightarrow> 'a MFOTL.formula \<Rightarrow> 'a vproof \<Rightarrow> bool" where
  "s_check vs f p = (case (f, p) of
    (MFOTL.TT, STT i) \<Rightarrow> True
  | (MFOTL.Pred r ts, SPred i s ts') \<Rightarrow> 
    (r = s \<and> ts = ts' \<and> {r} \<times> listset (map (eval_trm_set vs) ts) \<subseteq> \<Gamma> \<sigma> i)
  | (MFOTL.Eq t1 t2, SEq i t1' t2') \<Rightarrow> (t1 = t1' \<and> t2 = t2' \<and> undefined)
  | (MFOTL.Neg \<phi>, SNeg vp) \<Rightarrow> v_check vs \<phi> vp
  | (MFOTL.Or \<phi> \<psi>, SOrL sp1) \<Rightarrow> s_check vs \<phi> sp1
  | (MFOTL.Or \<phi> \<psi>, SOrR sp2) \<Rightarrow> s_check vs \<psi> sp2
  | (MFOTL.And \<phi> \<psi>, SAnd sp1 sp2) \<Rightarrow> s_check vs \<phi> sp1 \<and> s_check vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (MFOTL.Imp \<phi> \<psi>, SImplL vp1) \<Rightarrow> v_check vs \<phi> vp1
  | (MFOTL.Imp \<phi> \<psi>, SImplR sp2) \<Rightarrow> s_check vs \<psi> sp2
  | (MFOTL.Iff \<phi> \<psi>, SIffSS sp1 sp2) \<Rightarrow> s_check vs \<phi> sp1 \<and> s_check vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (MFOTL.Iff \<phi> \<psi>, SIffVV vp1 vp2) \<Rightarrow> v_check vs \<phi> vp1 \<and> v_check vs \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (MFOTL.Exists x \<phi>, SExists part) \<Rightarrow> undefined
  | (MFOTL.Forall x \<phi>, SForall part) \<Rightarrow> undefined
  | (MFOTL.Prev \<I> \<phi>, SPrev sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SPrev sp) in 
    i = Suc j \<and> mem (\<Delta> \<sigma> i) \<I> \<and> s_check vs \<phi> sp)
  | (MFOTL.Next \<I> \<phi>, SNext sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SNext sp) in
    j = Suc i \<and> mem (\<Delta> \<sigma> j) \<I> \<and> s_check vs \<phi> sp)
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
    \<and> map s_at sps = [li ..< Suc (LTP_p \<sigma> i \<I>)]
    \<and> (\<forall>sp \<in> set sps. s_check vs \<phi> sp))
  | (MFOTL.Always \<I> \<phi>, SAlways i hi sps) \<Rightarrow>
    (hi = (case right \<I> of enat b \<Rightarrow> LTP_f \<sigma> i b) 
    \<and> right \<I> \<noteq> \<infinity>
    \<and> map s_at sps = [(ETP_f \<sigma> i \<I>) ..< Suc hi]
    \<and> (\<forall>sp \<in> set sps. s_check vs \<phi> sp))
  | (MFOTL.Since \<phi> \<I> \<psi>, SSince sp2 sp1s) \<Rightarrow>
    (let i = s_at (SSince sp2 sp1s); j = s_at sp2 in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) \<I> 
    \<and> map s_at sp1s = [Suc j ..< Suc i] 
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
  | (MFOTL.Pred r ts, VPred i pred ts') \<Rightarrow> (r = pred \<and> ts = ts' \<and> 
    {r} \<times> listset (map (eval_trm_set vs) ts) \<subseteq> - \<Gamma> \<sigma> i)
  | (_, _) \<Rightarrow> False)"

end

end