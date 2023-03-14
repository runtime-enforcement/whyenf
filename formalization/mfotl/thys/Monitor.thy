(*<*)
theory Monitor
  imports Proof_System "HOL-Library.Simps_Case_Conv" 
begin
(*>*)

lemma Cons_eq_upt_conv: "x # xs = [m ..< n] \<longleftrightarrow> m < n \<and> x = m \<and> xs = [Suc m ..< n]"
  by (induct n arbitrary: xs) (force simp: Cons_eq_append_conv)+

lemma map_setE[elim_format]: "map f xs = ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x\<in>set xs. f x = y"
  by (induct xs arbitrary: ys) auto

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

context fixes \<sigma> :: "'d :: {default, linorder} MFOTL.trace"

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
  | (MFOTL.Forall x \<phi>, SForall y sp_part) \<Rightarrow> (let i = s_at (part_hd sp_part)
      in x = y \<and> (\<forall>(sub, sp) \<in> SubsVals sp_part. s_at sp = i \<and> (\<forall>z \<in> sub. s_check (v (x := z)) \<phi> sp)))
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
    (r = pred \<and> ts = ts' \<and> (r, MFOTL.eval_trms v ts) \<notin> \<Gamma> \<sigma> i)
  | (MFOTL.Neg \<phi>, VNeg sp) \<Rightarrow> s_check v \<phi> sp
  | (MFOTL.Or \<phi> \<psi>, VOr vp1 vp2) \<Rightarrow> v_check v \<phi> vp1 \<and> v_check v \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (MFOTL.And \<phi> \<psi>, VAndL vp1) \<Rightarrow> v_check v \<phi> vp1
  | (MFOTL.And \<phi> \<psi>, VAndR vp2) \<Rightarrow> v_check v \<psi> vp2
  | (MFOTL.Imp \<phi> \<psi>, VImp sp1 vp2) \<Rightarrow> s_check v \<phi> sp1 \<and> v_check v \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (MFOTL.Iff \<phi> \<psi>, VIffSV sp1 vp2) \<Rightarrow> s_check v \<phi> sp1 \<and> v_check v \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (MFOTL.Iff \<phi> \<psi>, VIffVS vp1 sp2) \<Rightarrow> v_check v \<phi> vp1 \<and> s_check v \<psi> sp2 \<and> v_at vp1 = s_at sp2
  | (MFOTL.Exists x \<phi>, VExists y vp_part) \<Rightarrow> (let i = v_at (part_hd vp_part)
      in x = y \<and> (\<forall>(sub, vp) \<in> SubsVals vp_part. v_at vp = i \<and> (\<forall>z \<in> sub. v_check (v (x := z)) \<phi> vp)))
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
simps_of_case s_check_simps[simp]: s_check.simps[unfolded prod.case] (splits: MFOTL.formula.split sproof.split)
simps_of_case v_check_simps[simp]: v_check.simps[unfolded prod.case] (splits: MFOTL.formula.split vproof.split)


lemma check_sound:
  "s_check v \<phi> sp \<Longrightarrow> SAT \<sigma> v (s_at sp) \<phi>"
  "v_check v \<phi> vp \<Longrightarrow> VIO \<sigma> v (v_at vp) \<phi>"
proof (induction sp and vp arbitrary: v \<phi> and v \<phi>)
  case STT
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.STT)
next
  case SPred
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SPred)
next
  case SNeg
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SNeg)
next
  case SAnd
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SAnd)
next
  case SOrL
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SOrL)
next
  case SOrR
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SOrR)
next
  case SImpR
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SImpR)
next
  case SImpL
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SImpL)
next
  case SIffSS
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SIffSS)
next
  case SIffVV
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SIffVV)
next
  case (SExists x z sp)
  with SExists(1)[of "v(x := z)"] show ?case
    by (cases \<phi>) (auto intro: SAT_VIO.SExists)
next
  case (SForall x part)
  then show ?case
  proof (cases \<phi>)
      case (Forall y \<psi>)
      show ?thesis unfolding Forall
      proof (intro SAT_VIO.SForall allI)
        fix z
        let ?sp = "lookup_part part z"
        from lookup_part_SubsVals[of z part] obtain D where "z \<in> D" "(D, ?sp) \<in> SubsVals part"
          by blast
        with SForall(2-) Forall have "s_check (v(y := z)) \<psi> ?sp" "s_at ?sp = s_at (SForall x part)"
          by auto
        then show "SAT \<sigma> (v(y := z)) (s_at (SForall x part)) \<psi>"
          by (auto simp del: fun_upd_apply dest!: SForall(1)[rotated])
      qed
    qed auto
next
  case (SSince spsi sps)
  then show ?case
  proof (cases \<phi>)
    case (Since \<phi> I \<psi>)
    show ?thesis
      using SSince
      unfolding Since
      apply (intro SAT_VIO.SSince[of "s_at spsi"])
         apply (auto simp: Let_def le_Suc_eq Cons_eq_append_conv Cons_eq_upt_conv
          split: if_splits list.splits)
      subgoal for k z zs
        apply (cases "k \<le> s_at z")
         apply (fastforce simp: le_Suc_eq elim!: map_setE[of _ _ _ k])+
        done
      done
  qed auto
next
  case (SOnce i sp)
  then show ?case
  proof (cases \<phi>)
    case (Once I \<phi>)
    show ?thesis
      using SOnce
      unfolding Once
      apply (intro SAT_VIO.SOnce[of "s_at sp"])
        apply (auto simp: Let_def)
      done
  qed auto
next
  case (SEventually i sp)
  then show ?case
  proof (cases \<phi>)
    case (Eventually I \<phi>)
    show ?thesis
      using SEventually
      unfolding Eventually
      apply (intro SAT_VIO.SEventually[of _ "s_at sp"])
        apply (auto simp: Let_def)
      done
  qed auto
next
  case SHistoricallyOut
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SHistoricallyOut)
next
  case (SHistorically i li sps)
  then show ?case
  proof (cases \<phi>)
    case (Historically I \<phi>)
    {fix k
      define j where j_def: "j \<equiv> case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP \<sigma> (\<tau>  \<sigma> i - n)"
      assume k_def: "k \<ge> j \<and> k \<le> i \<and> k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      from SHistorically Historically j_def have map: "set (map s_at sps) = set [j ..< Suc (LTP_p \<sigma> i I)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([j ..< Suc (LTP_p \<sigma> i I)])" using j_def k_def by auto
      then obtain x where x: "x \<in> set sps"  "s_at x = k" using k_def map
        apply auto
         apply (metis imageE insertI1)
        by (metis list.set_map imageE kset map)
      then have "SAT \<sigma> v k \<phi>" using SHistorically unfolding Historically
        by (auto simp: Let_def)
    } note * = this
    show ?thesis
      using SHistorically
      unfolding Historically
      apply (auto simp: Let_def intro!: SAT_VIO.SHistorically)
      using SHistorically.IH *  by (auto split: if_splits)
  qed (auto intro: SAT_VIO.intros)
next
  case (SAlways i hi sps)
  then show ?case
  proof (cases \<phi>)
    case (Always I \<phi>)
    obtain n where n_def: "right I = enat n"
      using SAlways
      by (auto simp: Always split: enat.splits)
    {fix k  
      define j where j_def: "j \<equiv> LTP \<sigma> (\<tau> \<sigma> i + n)"
      assume k_def: "k \<le> j \<and> k \<ge> i \<and> k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      from SAlways Always j_def have map: "set (map s_at sps) = set [(ETP_f \<sigma> i I) ..< Suc j]"
        by (auto simp: Let_def n_def)
      then have kset: "k \<in> set ([(ETP_f \<sigma> i I) ..< Suc j])" using k_def j_def by auto
      then obtain x where x: "x \<in> set sps" "s_at x = k" using k_def map
        apply auto
         apply (metis imageE insertI1)
        by (metis set_map imageE kset map)
      then have "SAT \<sigma> v k \<phi>" using SAlways unfolding Always
        by (auto simp: Let_def n_def)
    } note * = this
    then show ?thesis
      using SAlways
      unfolding Always
      by (auto simp: Let_def n_def intro: SAT_VIO.SAlways split: if_splits enat.splits)
  qed(auto intro: SAT_VIO.intros)
next
  case (SUntil sps spsi)
  then show ?case
  proof (cases \<phi>)
    case (Until \<phi> I \<psi>)
    show ?thesis
      using SUntil
      unfolding Until
      apply (intro SAT_VIO.SUntil[of _ "s_at spsi"])
         apply (auto simp: Let_def le_Suc_eq Cons_eq_append_conv Cons_eq_upt_conv
          split: if_splits list.splits)
      subgoal for k z zs
        apply (cases "k \<le> s_at z")
         apply (fastforce simp: le_Suc_eq elim!: map_setE[of _ _ _ k])+
        done
      done
  qed auto
next
  case (SNext sp)
  then show ?case by (cases \<phi>) (auto simp add: Let_def SAT_VIO.SNext)
next
  case (SPrev sp)
  then show ?case by (cases \<phi>) (auto simp add: Let_def SAT_VIO.SPrev)
next
  case VFF
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VFF)
next
  case VPred
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VPred)
next
  case VNeg
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VNeg)
next
  case VOr
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VOr)
next
  case VAndL
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VAndL)
next
  case VAndR
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VAndR)
next
  case VImp
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VImp)
next
  case VIffSV
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VIffSV)
next
  case VIffVS
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VIffVS)
next
  case (VExists x part)
  then show ?case
  proof (cases \<phi>)
      case (Exists y \<psi>)
      show ?thesis unfolding Exists
      proof (intro SAT_VIO.VExists allI)
        fix z
        let ?vp = "lookup_part part z"
        from lookup_part_SubsVals[of z part] obtain D where "z \<in> D" "(D, ?vp) \<in> SubsVals part"
          by blast
        with VExists(2-) Exists have "v_check (v(y := z)) \<psi> ?vp" "v_at ?vp = v_at (VExists x part)"
          by auto
        then show "VIO \<sigma> (v(y := z)) (v_at (VExists x part)) \<psi>"
          by (auto simp del: fun_upd_apply dest!: VExists(1)[rotated])
      qed
    qed auto
next
  case (VForall x z vp)
  with VForall(1)[of "v(x := z)"] show ?case
    by (cases \<phi>) (auto intro: SAT_VIO.VForall)
next
  case VOnceOut
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VOnceOut)
next
  case (VOnce i li vps)
  then show ?case
  proof (cases \<phi>)
    case (Once I \<phi>)
    {fix k
      define j where j_def: "j \<equiv> case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - n)"
      assume k_def: "k \<ge> j \<and> k \<le> i \<and> k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      from VOnce Once j_def have map: "set (map v_at vps) = set [j ..< Suc (LTP_p \<sigma> i I)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([j ..< Suc (LTP_p \<sigma> i I)])" using j_def k_def by auto
      then obtain x where x: "x \<in> set vps"  "v_at x = k" using k_def map
        apply auto
         apply (metis imageE insertI1)
        by (metis list.set_map imageE kset map)
      then have "VIO \<sigma> v k \<phi>" using VOnce unfolding Once
        by (auto simp: Let_def)
    } note * = this
    show ?thesis
      using VOnce
      unfolding Once
      apply (auto simp: Let_def intro!: SAT_VIO.VOnce)
      using VOnce.IH *  by (auto split: if_splits)
  qed (auto intro: SAT_VIO.intros)
next
  case (VEventually i hi vps)
  then show ?case
  proof (cases \<phi>)
    case (Eventually I \<phi>)
    obtain n where n_def: "right I = enat n"
      using VEventually
      by (auto simp: Eventually split: enat.splits)
    {fix k  
      define j where j_def: "j \<equiv> LTP \<sigma> (\<tau> \<sigma> i + n)"
      assume k_def: "k \<le> j \<and> k \<ge> i \<and> k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      from VEventually Eventually j_def have map: "set (map v_at vps) = set [(ETP_f \<sigma> i I) ..< Suc j]"
        by (auto simp: Let_def n_def)
      then have kset: "k \<in> set ([(ETP_f \<sigma> i I) ..< Suc j])" using k_def j_def by auto
      then obtain x where x: "x \<in> set vps" "v_at x = k" using k_def map
        apply auto
         apply (metis imageE insertI1)
        by (metis set_map imageE kset map)
      then have "VIO \<sigma> v k \<phi>" using VEventually unfolding Eventually
        by (auto simp: Let_def n_def)
    } note * = this
    then show ?thesis
      using VEventually
      unfolding Eventually
      by (auto simp: Let_def n_def intro: SAT_VIO.VEventually split: if_splits enat.splits)
  qed(auto intro: SAT_VIO.intros)
next
  case (VHistorically i vp)
  then show ?case
  proof (cases \<phi>)
    case (Historically I \<phi>)
    show ?thesis
      using VHistorically
      unfolding Historically
      apply (intro SAT_VIO.VHistorically[of "v_at vp"])
        apply (auto simp: Let_def)
      done
  qed auto
next
  case (VAlways i vp)
  then show ?case
  proof (cases \<phi>)
    case (Always I \<phi>)
    show ?thesis
      using VAlways
      unfolding Always
      apply (intro SAT_VIO.VAlways[of _ "v_at vp"])
        apply (auto simp: Let_def)
      done
  qed auto
next
  case VNext
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VNext)
next
  case VNextOutR
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VNextOutR)
next
  case VNextOutL
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VNextOutL)
next
  case VPrev
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VPrev)
next
  case VPrevOutR
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VPrevOutR)
next
  case VPrevOutL
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VPrevOutL)
next
  case VPrevZ
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VPrevZ)
next
  case VSinceOut
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VSinceOut)
next
  case (VSince i vp vps)
  then show ?case
  proof (cases \<phi>)
    case (Since \<phi> I \<psi>)
    {fix k
      assume k_def: "k \<ge> v_at vp \<and> k \<le> i \<and> k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      from VSince Since have map: "set (map v_at vps) = set ([(v_at vp) ..< Suc (LTP_p \<sigma> i I)])"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([(v_at vp) ..< Suc (LTP_p \<sigma> i I)])" using k_def by auto
      then obtain x where x: "x \<in> set vps" "v_at x = k" using k_def map kset
        apply auto
         apply (metis imageE insertI1)
        by (metis list.set_map imageE kset map)
      then have "VIO \<sigma> v k \<psi>" using VSince unfolding Since
        by (auto simp: Let_def)
    } note * = this
    show ?thesis
      using VSince
      unfolding Since
      apply (auto simp: Let_def split: enat.splits if_splits
          intro!: SAT_VIO.VSince[of _ i "v_at vp"])
      using VSince.IH * by (auto split: if_splits)
  qed (auto intro: SAT_VIO.intros)
next
  case (VUntil i vps vp)
  then show ?case
  proof (cases \<phi>)
    case (Until \<phi> I \<psi>)
    {fix k
      assume k_def: "k \<le> v_at vp \<and> k \<ge> i \<and> k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      from VUntil Until have map: "set (map v_at vps) = set [(ETP_f \<sigma> i I) ..< Suc (v_at vp)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([(ETP_f \<sigma> i I) ..< Suc (v_at vp)])" using k_def by auto
      then obtain x where x: "x \<in> set vps" "v_at x = k" using k_def map kset
        apply auto
         apply (metis imageE insertI1)
        by (metis list.set_map imageE kset map)
      then have "VIO \<sigma> v k \<psi>" using VUntil unfolding Until
        by (auto simp: Let_def)
    } note * = this
    then show ?thesis
      using VUntil
      unfolding Until
      by (auto simp: Let_def split: enat.splits if_splits
          intro!: SAT_VIO.VUntil)
  qed(auto intro: SAT_VIO.intros)
next
  case (VSinceInf i li vps)
  then show ?case
  proof (cases \<phi>)
    case (Since \<phi> I \<psi>)
    {fix k
      define j where j_def: "j \<equiv> case right I of \<infinity> \<Rightarrow> 0 | enat n \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - n)"
      assume k_def: "k \<ge> j \<and> k \<le> i \<and> k \<le> LTP \<sigma> (\<tau> \<sigma> i - left I)"
      from VSinceInf Since j_def have map: "set (map v_at vps) = set [j ..< Suc (LTP_p \<sigma> i I)]"
        by (auto simp: Let_def)
      then have kset: "k \<in> set ([j ..< Suc (LTP_p \<sigma> i I)])" using j_def k_def by auto
      then obtain x where x: "x \<in> set vps"  "v_at x = k" using k_def map
        apply auto
         apply (metis imageE insertI1)
        by (metis list.set_map imageE kset map)
      then have "VIO \<sigma> v k \<psi>" using VSinceInf unfolding Since
        by (auto simp: Let_def)
    } note * = this
    show ?thesis
      using VSinceInf
      unfolding Since
      apply (auto simp: Let_def intro!: SAT_VIO.VSinceInf)
      using VSinceInf.IH *  by (auto split: if_splits)
  qed (auto intro: SAT_VIO.intros)
next
  case (VUntilInf i hi vps)
  then show ?case
  proof (cases \<phi>)
    case (Until \<phi> I \<psi>)
    obtain n where n_def: "right I = enat n"
      using VUntilInf
      by (auto simp: Until split: enat.splits)
    {fix k  
      define j where j_def: "j \<equiv> LTP \<sigma> (\<tau> \<sigma> i + n)"
      assume k_def: "k \<le> j \<and> k \<ge> i \<and> k \<ge> ETP \<sigma> (\<tau> \<sigma> i + left I)"
      from VUntilInf Until j_def have map: "set (map v_at vps) = set [(ETP_f \<sigma> i I) ..< Suc j]"
        by (auto simp: Let_def n_def)
      then have kset: "k \<in> set ([(ETP_f \<sigma> i I) ..< Suc j])" using k_def j_def by auto
      then obtain x where x: "x \<in> set vps" "v_at x = k" using k_def map
        apply auto
         apply (metis imageE insertI1)
        by (metis list.set_map imageE kset map)
      then have "VIO \<sigma> v k \<psi>" using VUntilInf unfolding Until
        by (auto simp: Let_def n_def)
    } note * = this
    then show ?thesis
      using VUntilInf
      unfolding Until
      by (auto simp: Let_def n_def intro: SAT_VIO.VUntilInf split: if_splits enat.splits)
  qed(auto intro: SAT_VIO.intros)
qed

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
  | "positions (y#ys) x = (\<lambda>ns. if x = y then 0 # ns else ns) (map Suc (positions ys x))"

lemma eq_positions_iff: "length xs = length ys
  \<Longrightarrow> positions xs x = positions ys y \<longleftrightarrow> (\<forall>n< length xs. xs ! n = x \<longleftrightarrow> ys ! n = y)"
  apply (induct xs ys arbitrary: x y rule: list_induct2)
  using less_Suc_eq_0_disj by auto

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

lemma compatible_alt: 
  "compatible X vs v \<longleftrightarrow> v \<in> compatible_vals X vs"
  by (auto simp: compatible_def compatible_vals_def)

lemma compatible_empty_iff: "compatible {} vs v \<longleftrightarrow> True"
  by (auto simp: compatible_def)

lemma compatible_vals_empty_eq: "compatible_vals {} vs = UNIV"
  by (auto simp: compatible_vals_def)

lemma compatible_union_iff: 
  "compatible (X \<union> Y) vs v \<longleftrightarrow> compatible X vs v \<and> compatible Y vs v"
  by (auto simp: compatible_def)

lemma compatible_vals_union_eq: 
  "compatible_vals (X \<union> Y) vs = compatible_vals X vs \<inter> compatible_vals Y vs"
  by (auto simp: compatible_vals_def)

lemma compatible_antimono: 
  "compatible X vs v \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> compatible Y vs v"
  by (auto simp: compatible_def)

lemma compatible_vals_antimono: 
  "Y \<subseteq> X \<Longrightarrow> compatible_vals X vs \<subseteq> compatible_vals Y vs"
  by (auto simp: compatible_vals_def)

lemma compatible_extensible: 
  "(\<forall>x. vs x \<noteq> {}) \<Longrightarrow> compatible X vs v \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> \<exists>v'. compatible Y vs v' \<and> (\<forall>x\<in>X. v x = v' x)" 
  apply (rule_tac x="override_on v (\<lambda>x. SOME y. y \<in> vs x) (Y-X)" in exI)
  using some_in_eq[of "vs _"] by (auto simp: override_on_def compatible_def)

lemmas compatible_vals_extensible = compatible_extensible[unfolded compatible_alt]

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

unbundle MFOTL_notation \<comment> \<open> enable notation \<close>

text \<open> OBS: Even if there is an infinite set for @{term "\<^bold>v x"}, we can still get a 
 finite @{term mk_values} because it only cares about the latest set in the list
 for @{term "\<^bold>v ''x''"}. This is why the definition below has many cases. \<close>

term "''P'' \<dagger> [\<^bold>c (0::nat), \<^bold>v ''x'', \<^bold>v ''y'']"
value "mk_values [(\<^bold>c (0::nat), {0}), (\<^bold>v ''x'', Complement {0::nat, 1}), (\<^bold>v ''y'', {0::nat, 1}), (\<^bold>v ''x'', {0::nat, 1})]"

unbundle MFOTL_no_notation \<comment> \<open> disable notation \<close>

definition "mk_values_subset p tXs X 
  \<longleftrightarrow> (let (fintXs, inftXs) = partition (\<lambda>tX. finite (snd tX)) tXs in
  if inftXs = [] then {p} \<times> mk_values tXs \<subseteq> X 
  else let inf_dups = filter (\<lambda>tX. (fst tX) \<in> set (map fst fintXs)) inftXs in
    if inf_dups = [] then (if finite X then False else Code.abort STR ''subset on infinite subset'' (\<lambda>_. {p} \<times> mk_values tXs \<subseteq> X))
    else if list_all (\<lambda>tX. Max (set (positions tXs tX)) < Max (set (positions (map fst tXs) (fst tX)))) inf_dups
      then {p} \<times> mk_values tXs \<subseteq> X 
      else (if finite X then False else Code.abort STR ''subset on infinite subset'' (\<lambda>_. {p} \<times> mk_values tXs \<subseteq> X)))"

lemma set_Cons_eq: "set_Cons X XS = (\<Union>xs\<in>XS. (\<lambda>x. x # xs) ` X)"
  by (auto simp: set_Cons_def)

lemma set_Cons_empty_iff: "set_Cons X XS = {} \<longleftrightarrow> (X = {} \<or> XS = {})"
  by (auto simp: set_Cons_eq)

(* (\<Longleftarrow>) if for all (t,X) \<in> set tXs the latest Y's such that (t,Y) \<in> set tXs satisfy that Y \<noteq> {} *)
lemma mk_values_nemptyI: "\<forall>tX \<in> set tXs. snd tX \<noteq> {} \<Longrightarrow> mk_values tXs \<noteq> {}"
  by (induct tXs)
    (auto simp: Let_def set_Cons_eq split: prod.splits trm.splits)

lemma infinite_set_ConsI: 
  "XS \<noteq> {} \<Longrightarrow> infinite X \<Longrightarrow> infinite (set_Cons X XS)"
  "X \<noteq> {} \<Longrightarrow> infinite XS \<Longrightarrow> infinite (set_Cons X XS)"
proof(unfold set_Cons_eq)
  assume "infinite X" and "XS \<noteq> {}"
  then obtain xs where "xs \<in> XS"
    by blast
  hence "inj (\<lambda>x. x # xs)"
    by (clarsimp simp: inj_on_def)
  hence "infinite ((\<lambda>x. x # xs) ` X)"
    using \<open>infinite X\<close> finite_imageD inj_on_def 
    by blast
  moreover have "((\<lambda>x. x # xs) ` X) \<subseteq> (\<Union>xs\<in>XS. (\<lambda>x. x # xs) ` X)"
    using \<open>xs \<in> XS\<close> by auto
  ultimately show "infinite (\<Union>xs\<in>XS. (\<lambda>x. x # xs) ` X)"
    by (simp add: infinite_super)
next
  assume "infinite XS" and "X \<noteq> {}"
  hence disjf: "disjoint_family_on (\<lambda>xs. (\<lambda>x. x # xs) ` X) XS"
    by (auto simp: disjoint_family_on_def)
  moreover have "x \<in> XS \<Longrightarrow> (\<lambda>xs. xs # x) ` X \<noteq> {}" for x
    using \<open>X \<noteq> {}\<close> by auto
  ultimately show "infinite (\<Union>xs\<in>XS. (\<lambda>x. x # xs) ` X)"
    using infinite_disjoint_family_imp_infinite_UNION[OF \<open>infinite XS\<close> _ disjf]
    by auto
qed

(* TODO: clean duplicated proofs *)
lemma infinite_mk_values1: "\<forall>tX \<in> set tXs. snd tX \<noteq> {} \<Longrightarrow> tY \<in> set tXs 
  \<Longrightarrow> \<forall>Y. (fst tY, Y) \<in> set tXs \<longrightarrow> infinite Y \<Longrightarrow> infinite (mk_values tXs)"
proof (induct tXs arbitrary: tY)
  case (Cons tX tXs)
  show ?case
  proof (cases "tY \<in> set tXs")
    case True
    then show ?thesis
    proof (auto simp add: Let_def image_iff split: prod.splits trm.splits,
      goal_cases var_in var_out const)
      case (var_in X x Y)
      hence "\<forall>Z. (fst (trm.Var x, Y), Z) \<in> set tXs \<longrightarrow> infinite Z"
        and "\<forall>tX\<in>set tXs. snd tX \<noteq> {}"
        by (metis (no_types, lifting) Cons.hyps Cons.prems(1) Cons.prems(3) 
            finite_imageD inj_on_def list.inject list.set_intros(2))
          (simp add: Cons.prems(1))
      hence "infinite (mk_values tXs)"
        using Cons.hyps[OF _ \<open>(trm.Var x, Y) \<in> set tXs\<close>]
        by auto
      moreover have "inj (\<lambda>xs. xs ! hd (positions (map fst tXs) (trm.Var x)) # xs)"
        by (clarsimp simp: inj_on_def)
      ultimately show ?case
        using var_in(4) finite_imageD inj_on_subset by fastforce
    next
      case (var_out Y x)
      hence "infinite Y"
        using Cons.prems
        by (simp add: Cons.hyps infinite_set_ConsI(2))
      moreover have "mk_values tXs \<noteq> {}"
        using Cons.prems 
        by (auto intro!: mk_values_nemptyI)
      then show ?case
        using Cons var_out infinite_set_ConsI(1)[OF \<open>mk_values tXs \<noteq> {}\<close> \<open>infinite Y\<close>]
        by auto
    next
      case (const Y c)
      hence "infinite Y"
        using Cons.prems
        by (simp add: Cons.hyps infinite_set_ConsI(2))
      moreover have "mk_values tXs \<noteq> {}"
        using Cons.prems 
        by (auto intro!: mk_values_nemptyI)
      then show ?case
        using Cons const infinite_set_ConsI(1)[OF \<open>mk_values tXs \<noteq> {}\<close> \<open>infinite Y\<close>]
        by auto
    qed
  next
    case False
    then show ?thesis
    proof (auto simp add: Let_def image_iff split: prod.splits trm.splits,
      goal_cases var_in var_out const)
      case (var_in X x Y)
      hence "\<forall>Z. (fst (trm.Var x, Y), Z) \<in> set tXs \<longrightarrow> infinite Z"
        and "\<forall>tX\<in>set tXs. snd tX \<noteq> {}"
        using Cons.prems
        by auto
      hence "infinite (mk_values tXs)"
        using Cons.hyps[OF _ \<open>(trm.Var x, Y) \<in> set tXs\<close>]
        by auto
      moreover have "inj (\<lambda>xs. xs ! hd (positions (map fst tXs) (trm.Var x)) # xs)"
        by (clarsimp simp: inj_on_def)
      ultimately show ?case
        using var_in(4) finite_imageD inj_on_subset by fastforce
    next
      case (var_out Y x)
      hence "infinite Y"
        using Cons.prems False
        by (simp add: Cons.hyps infinite_set_ConsI(2))
      moreover have "mk_values tXs \<noteq> {}"
        using Cons.prems 
        by (auto intro!: mk_values_nemptyI)
      then show ?case
        using Cons var_out infinite_set_ConsI(1)[OF \<open>mk_values tXs \<noteq> {}\<close> \<open>infinite Y\<close>]
        by auto
    next
      case (const Y c)
      hence "infinite Y"
        using Cons.prems
        by (simp add: Cons.hyps infinite_set_ConsI(2))
      moreover have "mk_values tXs \<noteq> {}"
        using Cons.prems 
        by (auto intro!: mk_values_nemptyI)
      then show ?case
        using Cons const infinite_set_ConsI(1)[OF \<open>mk_values tXs \<noteq> {}\<close> \<open>infinite Y\<close>]
        by auto
    qed
  qed
qed simp

lemma mk_values_subset_iff: "\<forall>tX \<in> set tXs. snd tX \<noteq> {} 
  \<Longrightarrow> mk_values_subset p tXs X \<longleftrightarrow> {p} \<times> mk_values tXs \<subseteq> X"
proof (clarsimp simp: mk_values_subset_def image_iff Let_def comp_def, safe)
  assume "\<forall>tX\<in>set tXs. snd tX \<noteq> {}" and "finite X" 
    and filter1: "filter (\<lambda>x. infinite (snd x) \<and> (\<exists>b. (fst x, b) \<in> set tXs \<and> finite b)) tXs = []" 
    and filter2: "filter (\<lambda>x. infinite (snd x)) tXs \<noteq> []"
  then obtain tY where "tY \<in> set tXs" and "infinite (snd tY)"
    by auto (metis (mono_tags, lifting) filter_False prod.collapse)
  moreover have "\<forall>Y. (fst tY, Y) \<in> set tXs \<longrightarrow> infinite Y"
    using filter1 calculation
    by auto (metis (mono_tags, lifting) filter_empty_conv)
  ultimately have "infinite (mk_values tXs)"
    using infinite_mk_values1[OF \<open>\<forall>tX\<in>set tXs. snd tX \<noteq> {}\<close>] 
    by auto
  hence "infinite ({p} \<times> mk_values tXs)"
    using finite_cartesian_productD2 by auto
  thus "{p} \<times> mk_values tXs \<subseteq> X \<Longrightarrow> False"
    using \<open>finite X\<close>
    by (simp add: finite_subset)
next
  assume "\<forall>tX\<in>set tXs. snd tX \<noteq> {}" 
    and "finite X" 
    and ex_dupl_inf: "\<not> list_all (\<lambda>tX. Max (set (positions tXs tX)) < Max (set (positions (map fst tXs) (fst tX))))
        (filter (\<lambda>x. infinite (snd x) \<and> (\<exists>b. (fst x, b) \<in> set tXs \<and> finite b)) tXs)" 
    and filter: "filter (\<lambda>x. infinite (snd x)) tXs \<noteq> []"
  thus "{p} \<times> mk_values tXs \<subseteq> X \<Longrightarrow> False"
    sorry
qed

fun s_check_exec :: "'d MFOTL.envset \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd sproof \<Rightarrow> bool"
  and v_check_exec :: "'d MFOTL.envset \<Rightarrow> 'd MFOTL.formula \<Rightarrow> 'd vproof \<Rightarrow> bool" where
  "s_check_exec vs f p = (case (f, p) of
    (MFOTL.TT, STT i) \<Rightarrow> True
  | (MFOTL.Pred r ts, SPred i s ts') \<Rightarrow> 
    (r = s \<and> ts = ts' \<and> mk_values_subset r (MFOTL.eval_trms_set vs ts) (\<Gamma> \<sigma> i))
  | (MFOTL.Neg \<phi>, SNeg vp) \<Rightarrow> v_check_exec vs \<phi> vp
  | (MFOTL.Or \<phi> \<psi>, SOrL sp1) \<Rightarrow> s_check_exec vs \<phi> sp1
  | (MFOTL.Or \<phi> \<psi>, SOrR sp2) \<Rightarrow> s_check_exec vs \<psi> sp2
  | (MFOTL.And \<phi> \<psi>, SAnd sp1 sp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> s_check_exec vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (MFOTL.Imp \<phi> \<psi>, SImpL vp1) \<Rightarrow> v_check_exec vs \<phi> vp1
  | (MFOTL.Imp \<phi> \<psi>, SImpR sp2) \<Rightarrow> s_check_exec vs \<psi> sp2
  | (MFOTL.Iff \<phi> \<psi>, SIffSS sp1 sp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> s_check_exec vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (MFOTL.Iff \<phi> \<psi>, SIffVV vp1 vp2) \<Rightarrow> v_check_exec vs \<phi> vp1 \<and> v_check_exec vs \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (MFOTL.Exists x \<phi>, SExists y val sp) \<Rightarrow> (x = y \<and> s_check_exec (vs (x := {val})) \<phi> sp)
  | (MFOTL.Forall x \<phi>, SForall y sp_part) \<Rightarrow> (let i = s_at (part_hd sp_part)
      in x = y \<and> (\<forall>(sub, sp) \<in> SubsVals sp_part. s_at sp = i \<and> s_check_exec (vs (x := sub)) \<phi> sp))
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
  | (MFOTL.Exists x \<phi>, VExists y vp_part) \<Rightarrow> (let i = v_at (part_hd vp_part)
      in x = y \<and> (\<forall>(sub, vp) \<in> SubsVals vp_part. v_at vp = i \<and> v_check_exec (vs (x := sub)) \<phi> vp))
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

unbundle MFOTL_notation \<comment> \<open> enable notation \<close>

lemma mk_values_sound: "cs \<in> mk_values (MFOTL.eval_trms_set vs ts) 
  \<Longrightarrow> \<exists>v\<in>compatible_vals (fv (p \<dagger> ts)) vs. cs = MFOTL.eval_trms v ts"
proof (induct ts arbitrary: cs vs)
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
      then obtain a as
        where as_head: "as ! (hd (positions (map fst ?Ts) (\<^bold>v x))) = a"
          and as_tail: "as \<in> mk_values (MFOTL.eval_trms_set vs ts)" 
          and as_shape: "cs = a # as"
        using Cons(2) 
        by (clarsimp simp add: MFOTL.eval_trms_set_def Var image_iff)
      obtain v where v_hyps: "v \<in> compatible_vals (fv (p \<dagger> ts)) vs"
        "as = MFOTL.eval_trms v ts"
        using Cons(1)[OF as_tail] by blast
      hence as'_nth: "as ! n = v x"
        using nth_n positions_length[OF n_in]
        by (simp add: MFOTL.eval_trms_def)
      have evals_neq_Nil: "?evals vs ts \<noteq> []"
        using key by auto
      moreover have "positions (map fst (MFOTL.eval_trms_set vs ts)) (\<^bold>v x) \<noteq> []"
        using positions_eq_nil_iff[of "map fst ?Ts" "\<^bold>v x"] key
        by fastforce
      ultimately have as_hyp: "a = as ! n"
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
        subgoal for a as
          using Cons(1)[of as vs] 
          apply (clarsimp simp: MFOTL.eval_trms_set_def MFOTL.eval_trms_def compatible_vals_def)
          apply (rule_tac x="v(x := a)" in exI, clarsimp)
          apply (rule eval_trm_fv_cong, clarsimp)
          subgoal for v t'
            by (auto intro: trm.exhaust[where y=t'])
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

lemma fst_eval_trm_set[simp]: 
  "fst (MFOTL.eval_trm_set vs t) = t"
  by (cases t; clarsimp)

lemma map_fst_eval_trm_set [simp]:
  "map (fst \<circ> MFOTL.eval_trm_set vs) ts = ts"
  by (induct ts arbitrary: vs) auto

lemma mk_values_complete: "cs = MFOTL.eval_trms v ts 
  \<Longrightarrow> v \<in> compatible_vals (fv (p \<dagger> ts)) vs
  \<Longrightarrow> cs \<in> mk_values (MFOTL.eval_trms_set vs ts)"
proof (induct ts arbitrary: v cs vs)
  case (Cons t ts)
  then obtain a as 
    where a_def: "a = MFOTL.eval_trm v t" 
      and as_def: "as = MFOTL.eval_trms v ts"
      and cs_cons: "cs = a # as"
    by (auto simp: MFOTL.eval_trms_def)
  have compat_v_vs: "v \<in> compatible_vals (fv (p \<dagger> (ts))) vs" 
    using Cons.prems
    by (auto simp: compatible_vals_def)
  hence mk_values_ts: "as \<in> mk_values (map (MFOTL.eval_trm_set vs) ts)"
    using Cons.hyps[OF as_def] 
    unfolding MFOTL.eval_trms_set_def by blast
  show ?case
  proof (cases "t")
    case (Var x)
    then show ?thesis
    proof (cases "\<^bold>v x \<in> set ts")
      case True
      then obtain n 
        where n_head: "n = hd (positions ts (\<^bold>v x))"
          and n_in: "n \<in> set (positions ts (\<^bold>v x))"
          and nth_n: "ts ! n = \<^bold>v x"
        by (simp_all add: hd_positions_eq_fst_pos nth_fst_pos fst_pos_in_positions)
      hence n_in': "n = hd (positions (map fst (MFOTL.eval_trms_set vs ts)) (\<^bold>v x))"
        by (clarsimp simp: MFOTL.eval_trms_set_def)
      moreover have "as ! n = a"
        using a_def as_def nth_n Var n_in True positions_length
        by (fastforce simp: MFOTL.eval_trms_def)
      moreover have "\<^bold>v x \<in> set (map fst (MFOTL.eval_trms_set vs ts))"
        using True by (induct ts)
          (auto simp: MFOTL.eval_trms_set_def)
      ultimately show ?thesis
        using mk_values_ts cs_cons
        by (clarsimp simp: MFOTL.eval_trms_set_def Var image_iff)
    next
      case False
      then show ?thesis
        using Var cs_cons mk_values_ts Cons.prems a_def
        by (clarsimp simp: MFOTL.eval_trms_set_def image_iff 
            set_Cons_def compatible_vals_def split: MFOTL.trm.splits)
    qed
  next
    case (Const a)
    then show ?thesis 
      using cs_cons mk_values_ts Cons.prems a_def
      by (clarsimp simp: MFOTL.eval_trms_set_def image_iff
            set_Cons_def compatible_vals_def split: MFOTL.trm.splits)
  qed
qed (simp add: compatible_vals_def 
    MFOTL.eval_trms_set_def MFOTL.eval_trms_def)


definition AD :: "'d MFOTL.formula \<Rightarrow> nat \<Rightarrow> 'd set"
  where "AD \<phi> i = (\<Union> k < the (LRTP \<sigma> \<phi> i). \<Union> (set ` snd ` \<Gamma> \<sigma> (the_enat k)))"

lemma val_in_AD_iff:
  "x \<in> fv \<phi> \<Longrightarrow> v x \<in> AD \<phi> i \<longleftrightarrow> (\<exists>p ts k. k < the (LRTP \<sigma> \<phi> i) \<and> (p, MFOTL.eval_trms v ts) \<in> \<Gamma> \<sigma> (the_enat k) \<and> x \<in> \<Union> (set (map fv\<^sub>t ts)))"
  apply (intro iffI; clarsimp)
   apply (auto simp: AD_def)[1]
   apply (rename_tac k' p' cs)
   apply (rule_tac x=p' in exI)
   apply (rule_tac x="map (\<lambda>c. if v x = c then (\<^bold>v x::'d MFOTL.trm) else \<^bold>c c) cs" in exI)
   apply (rule_tac x=k' in exI)
   apply (auto simp: MFOTL.eval_trms_def)[1]
  subgoal for k' p' cs
    apply (subgoal_tac "map (MFOTL.eval_trm v \<circ> (\<lambda>c. if v x = c then \<^bold>v x else \<^bold>c c)) cs = cs")
     apply clarsimp
    apply (simp add: map_idI)
    done
  subgoal for p' cs k t'
    apply (cases t'; clarsimp)
    sorry
  done

lemma val_notin_AD_iff:
  "x \<in> fv \<phi> \<Longrightarrow> v x \<notin> AD \<phi> i \<longleftrightarrow> (\<forall>p ts k. k < the (LRTP \<sigma> \<phi> i) \<longrightarrow> x \<in> \<Union> (set (map fv\<^sub>t ts)) \<longrightarrow> (p, MFOTL.eval_trms v ts) \<notin> \<Gamma> \<sigma> (the_enat k))"
  using val_in_AD_iff 
  by blast

lemma compatible_vals_fun_upd: "compatible_vals A (vs(x := X)) =
  (if x \<in> A then {v \<in> compatible_vals (A - {x}) vs. v x \<in> X} else compatible_vals A vs)"
  unfolding compatible_vals_def
  by auto

lemma fun_upd_in_compatible_vals: "v \<in> compatible_vals (A - {x}) vs \<Longrightarrow> v(x := t) \<in> compatible_vals (A - {x}) vs"
  unfolding compatible_vals_def
  by auto

lemma fun_upd_in_compatible_vals_notin: "x \<notin> A \<Longrightarrow> v \<in> compatible_vals A vs \<Longrightarrow> v(x := t) \<in> compatible_vals A vs"
  unfolding compatible_vals_def
  by auto

lemma finite_values: "finite (\<Union> (set ` snd ` \<Gamma> \<sigma> (the_enat k)))"
  by (transfer, auto simp add: sfstfinite_def)

lemma finite_tps: "MFOTL.future_bounded \<phi> \<Longrightarrow> finite (\<Union> k < the (LRTP \<sigma> \<phi> i). {k})"
  using bounded_future_LRTP[of \<phi>] finite_enat_bounded 
  by simp

lemma finite_AD: "MFOTL.future_bounded \<phi> \<Longrightarrow> finite (AD \<phi> i)"
  using finite_tps finite_values
  by (simp add: AD_def enat_def)

lemma part_hd_tabulate: 
  assumes "MFOTL.future_bounded \<phi>"
    and "v_at (f (SOME z. z \<notin> local.AD \<phi> i)) = i"
  shows "v_at (part_hd (tabulate (sorted_list_of_set (AD \<phi> i)) f (f (SOME z. z \<notin> AD \<phi> i)))) = i"
  using assms
  apply transfer
  apply simp
  subgoal for \<phi> f \<sigma> i
  proof -
    assume "MFOTL.future_bounded \<phi>"
    then have eq: "set (sorted_list_of_set (Monitor.AD \<sigma> \<phi> i)) = UNIV = (Monitor.AD \<sigma> \<phi> i = UNIV)"
      by (simp add: Monitor.finite_AD)
    show ?thesis
      apply (rule impI)
      apply (simp only: eq)
      sorry
  qed
  done

lemma check_fv_cong:
  assumes "\<forall>x \<in> fv \<phi>. v x = v' x"
  shows "s_check v \<phi> sp \<longleftrightarrow> s_check v' \<phi> sp" "v_check v \<phi> vp \<longleftrightarrow> v_check v' \<phi> vp"
  using assms
proof (induct \<phi> arbitrary: v v' sp vp)
  case TT
  {
    case 1
    then show ?case
      by (cases sp) auto
  next
    case 2
    then show ?case
      by (cases vp) auto
  }
next
  case FF
  {
    case 1
    then show ?case
      by (cases sp) auto
  next
    case 2
    then show ?case 
      by (cases vp) auto
  }
next
  case (Pred p ts)
  {
    case 1
    with Pred show ?case using eval_trms_fv_cong[of ts v v']
      by (cases sp) auto
  next
    case 2
    with Pred show ?case using eval_trms_fv_cong[of ts v v']
      by (cases vp) auto
  }
next
  case (Neg \<phi>)
  {
    case 1
    with Neg[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Neg[of v v'] show ?case 
      by (cases vp) auto
  }
next
  case (Or \<phi>1 \<phi>2)
  {
    case 1
    with Or[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Or[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (And \<phi>1 \<phi>2)
  {
    case 1
    with And[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with And[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Imp \<phi>1 \<phi>2)
  {
    case 1
    with Imp[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Imp[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Iff \<phi>1 \<phi>2)
  {
    case 1
    with Iff[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Iff[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Exists x \<phi>)
  {
    case 1
    with Exists[of "v(x := z)" "v'(x := z)" for z] show ?case
      by (cases sp) (auto simp: fun_upd_def)
  next
    case 2
    with Exists[of "v(x := z)" "v'(x := z)" for z] show ?case
      by (cases vp) (auto simp: fun_upd_def)
  }
next
  case (Forall x \<phi>)
  {
    case 1
    with Forall[of "v(x := z)" "v'(x := z)" for z] show ?case
      by (cases sp) (auto simp: fun_upd_def)
  next
    case 2
    with Forall[of "v(x := z)" "v'(x := z)" for z] show ?case
      by (cases vp) (auto simp: fun_upd_def)
  }
next
  case (Prev I \<phi>)
  {
    case 1
    with Prev[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Prev[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Next I \<phi>)
  {
    case 1
    with Next[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Next[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Once I \<phi>)
  {
    case 1
    with Once[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Once[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Historically I \<phi>)
  {
    case 1
    with Historically[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Historically[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Eventually I \<phi>)
  {
    case 1
    with Eventually[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Eventually[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Always I \<phi>)
  {
    case 1
    with Always[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Always[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Since \<phi>1 I \<phi>2)
  {
    case 1
    with Since[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Since[of v v'] show ?case
      by (cases vp) auto
  }
next
  case (Until \<phi>1 I \<phi>2)
  {
    case 1
    with Until[of v v'] show ?case
      by (cases sp) auto
  next
    case 2
    with Until[of v v'] show ?case
      by (cases vp) auto
  }
qed

lemma s_check_fun_upd_notin[simp]:
  "x \<notin> fv \<phi> \<Longrightarrow> s_check (v(x := t)) \<phi> sp = s_check v \<phi> sp"
  by (rule check_fv_cong) auto
lemma v_check_fun_upd_notin[simp]:
  "x \<notin> fv \<phi> \<Longrightarrow> v_check (v(x := t)) \<phi> sp = v_check v \<phi> sp"
  by (rule check_fv_cong) auto

lemma SubsVals_nonempty: "(X, t) \<in> SubsVals part \<Longrightarrow> X \<noteq> {}"
  by transfer (auto simp: partition_on_def image_iff)

lemma ball_swap: "(\<forall>x \<in> A. \<forall>y \<in> B. P x y) = (\<forall>y \<in> B. \<forall>x \<in> A. P x y)"
  by auto

lemma check_exec_check:
  assumes "compatible_vals (fv \<phi>) vs \<noteq> {}" and "\<forall>x. vs x \<noteq> {}"
  shows "s_check_exec vs \<phi> sp \<longleftrightarrow> (\<forall>v \<in> compatible_vals (fv \<phi>) vs. s_check v \<phi> sp)" 
    and "v_check_exec vs \<phi> vp \<longleftrightarrow> (\<forall>v \<in> compatible_vals (fv \<phi>) vs. v_check v \<phi> vp)"
  using assms
proof (induct \<phi> arbitrary: vs sp vp)
  case TT
  {
    case 1
    then show ?case
      by (cases sp)
        auto
  next
    case 2
    then show ?case 
      by auto
  }
next
  case FF
  {
    case 1
    then show ?case 
      by (cases sp)
        auto
  next
    case 2
    then show ?case 
      by (cases vp)
        auto
  }
next
  case (Pred p ts)
  {
    case 1
    have obs: "\<forall>tX\<in>set (MFOTL.eval_trms_set vs ts). snd tX \<noteq> {}"
      using \<open>\<forall>x. vs x \<noteq> {}\<close>
      by (induct ts; clarsimp simp: MFOTL.eval_trms_set_def)
        (rule_tac y=a in MFOTL.trm.exhaust; clarsimp)
    show ?case
      using 1
      apply (cases sp; clarsimp simp: mk_values_subset_iff[OF obs] subset_eq  simp del: fv.simps)
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
      apply (metis MFOTL.eval_trms_set_def mk_values_complete)
      using mk_values_sound apply blast
        using mk_values_sound apply blast
        by (metis MFOTL.eval_trms_set_def mk_values_sound)
  }
next
  case (Neg \<phi>)
  {
    case 1
    then show ?case
      using Neg.hyps(2)
      by (cases sp) auto
  next
    case 2
    then show ?case 
      using Neg.hyps(1)
      by (cases vp) auto
  }
next
  case (Or \<phi>1 \<phi>2)
  {
    case 1
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 1(1) show ?case
    proof (cases sp)
      case (SOrL sp')
      from check_fv_cong(1)[of \<phi>1 _ _ sp'] show ?thesis
        unfolding SOrL s_check_exec_simps s_check_simps fv.simps Or(1)[OF comp_fv(1) 1(2), of sp']
        by (metis (mono_tags, lifting) 1(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
    next
      case (SOrR sp')
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SOrR s_check_exec_simps s_check_simps fv.simps Or(3)[OF comp_fv(2) 1(2), of sp']
        by (metis (mono_tags, lifting) 1(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 2(1) show ?case
    proof (cases vp)
      case (VOr vp1 vp2)
      from check_fv_cong(2)[of \<phi>1 _ _ vp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding VOr v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
           Or(2)[OF comp_fv(1) 2(2), of vp1]  Or(4)[OF comp_fv(2) 2(2), of vp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 2(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 2(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis 2(1) equals0I fv.simps(5))
        done
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (And \<phi>1 \<phi>2)
  {
    case 1
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 1(1) show ?case
    proof (cases sp)
      case (SAnd sp1 sp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(1)[of \<phi>2 _ _ sp2] show ?thesis
        unfolding SAnd s_check_exec_simps s_check_simps fv.simps ball_conj_distrib
           And(1)[OF comp_fv(1) 1(2), of sp1] And(3)[OF comp_fv(2) 1(2), of sp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 1(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 1(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis 1(1) equals0I fv.simps(6))
        done
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 2(1) show ?case
    proof (cases vp)
      case (VAndL vp')
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding VAndL v_check_exec_simps v_check_simps fv.simps And(2)[OF comp_fv(1) 2(2), of vp']
        by (metis (mono_tags, lifting) 2(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
    next
      case (VAndR vp')
      from check_fv_cong(2)[of \<phi>2 _ _ vp'] show ?thesis
        unfolding VAndR v_check_exec_simps v_check_simps fv.simps And(4)[OF comp_fv(2) 2(2), of vp']
        by (metis (mono_tags, lifting) 2(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (Imp \<phi>1 \<phi>2)
  {
    case 1
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 1(1) show ?case
    proof (cases sp)
      case (SImpL vp')
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding SImpL s_check_exec_simps s_check_simps fv.simps Imp(2)[OF comp_fv(1) 1(2), of vp']
        by (metis (mono_tags, lifting) 1(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
    next
      case (SImpR sp')
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SImpR s_check_exec_simps s_check_simps fv.simps Imp(3)[OF comp_fv(2) 1(2), of sp']
        by (metis (mono_tags, lifting) 1(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 2(1) show ?case
    proof (cases vp)
      case (VImp sp1 vp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding VImp v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
           Imp(1)[OF comp_fv(1) 2(2), of sp1] Imp(4)[OF comp_fv(2) 2(2), of vp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 2(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 2(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis 2(1) equals0I fv.simps(7))
        done
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (Iff \<phi>1 \<phi>2)
  {
    case 1
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 1(1) show ?case
    proof (cases sp)
      case (SIffSS sp1 sp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(1)[of \<phi>2 _ _ sp2] show ?thesis
        unfolding SIffSS s_check_exec_simps s_check_simps fv.simps ball_conj_distrib
           Iff(1)[OF comp_fv(1) 1(2), of sp1] Iff(3)[OF comp_fv(2) 1(2), of sp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 1(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 1(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis 1(1) equals0I fv.simps(8))
        done
    next
      case (SIffVV vp1 vp2)
      from check_fv_cong(2)[of \<phi>1 _ _ vp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding SIffVV s_check_exec_simps s_check_simps fv.simps ball_conj_distrib
           Iff(2)[OF comp_fv(1) 1(2), of vp1] Iff(4)[OF comp_fv(2) 1(2), of vp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 1(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 1(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis 1(1) equals0I fv.simps(8))
        done
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 2(1) show ?case
    proof (cases vp)
      case (VIffSV sp1 vp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding VIffSV v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
           Iff(1)[OF comp_fv(1) 2(2), of sp1] Iff(4)[OF comp_fv(2) 2(2), of vp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 2(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 2(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis 2(1) equals0I fv.simps(8))
        done
    next
      case (VIffVS vp1 sp2)
      from check_fv_cong(2)[of \<phi>1 _ _ vp1] check_fv_cong(1)[of \<phi>2 _ _ sp2] show ?thesis
        unfolding VIffVS v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
           Iff(2)[OF comp_fv(1) 2(2), of vp1] Iff(3)[OF comp_fv(2) 2(2), of sp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 2(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 2(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis 2(1) equals0I fv.simps(8))
        done
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (Exists x \<phi>)
  {
    case 1
    then have "(vs(x := Z)) y \<noteq> {}" if "Z \<noteq> {}" for Z y
      using that by auto
    with 1 have IH:
    "s_check_exec (vs(x := {z})) \<phi> sp = (\<forall>v\<in>compatible_vals (fv \<phi>) (vs(x := {z})). s_check v \<phi> sp)"
    for z sp
      by (intro Exists;
         auto simp: compatible_vals_fun_upd fun_upd_same
            simp del: fun_upd_apply intro: fun_upd_in_compatible_vals)+
    from 1(1) show ?case
      by (cases sp) (auto simp: SubsVals_nonempty IH fun_upd_in_compatible_vals_notin compatible_vals_fun_upd)
  next
case 2
    then have "(vs(x := Z)) y \<noteq> {}" if "Z \<noteq> {}" for Z y
      using that by auto
    with 2 have IH:
    "Z \<noteq> {} \<Longrightarrow> v_check_exec (vs(x := Z)) \<phi> vp = (\<forall>v\<in>compatible_vals (fv \<phi>) (vs(x := Z)). v_check v \<phi> vp)"
    for Z vp
      by (intro Exists;
         auto simp: compatible_vals_fun_upd fun_upd_same
            simp del: fun_upd_apply intro: fun_upd_in_compatible_vals)+
    show ?case
      by (cases vp)
        (auto simp: SubsVals_nonempty IH[OF SubsVals_nonempty]
        fun_upd_in_compatible_vals fun_upd_in_compatible_vals_notin compatible_vals_fun_upd
        ball_conj_distrib 2(1)[simplified] split: prod.splits if_splits |
        drule bspec, (assumption | rule 2(1)[simplified, folded ex_in_conv, THEN someI_ex]))+
  }
next
  case (Forall x \<phi>)
  {
    case 1
    then have "(vs(x := Z)) y \<noteq> {}" if "Z \<noteq> {}" for Z y
      using that by auto
    with 1 have IH:
    "Z \<noteq> {} \<Longrightarrow> s_check_exec (vs(x := Z)) \<phi> sp = (\<forall>v\<in>compatible_vals (fv \<phi>) (vs(x := Z)). s_check v \<phi> sp)"
    for Z sp
      by (intro Forall;
         auto simp: compatible_vals_fun_upd fun_upd_same
            simp del: fun_upd_apply intro: fun_upd_in_compatible_vals)+
    show ?case
      by (cases sp)
        (auto simp: SubsVals_nonempty IH[OF SubsVals_nonempty]
        fun_upd_in_compatible_vals fun_upd_in_compatible_vals_notin compatible_vals_fun_upd
        ball_conj_distrib 1(1)[simplified] split: prod.splits if_splits |
        drule bspec, (assumption | rule 1(1)[simplified, folded ex_in_conv, THEN someI_ex]))+
  next
    case 2
    then have "(vs(x := Z)) y \<noteq> {}" if "Z \<noteq> {}" for Z y
      using that by auto
    with 2 have IH:
    "v_check_exec (vs(x := {z})) \<phi> vp = (\<forall>v\<in>compatible_vals (fv \<phi>) (vs(x := {z})). v_check v \<phi> vp)"
    for z vp
      by (intro Forall;
         auto simp: compatible_vals_fun_upd fun_upd_same
            simp del: fun_upd_apply intro: fun_upd_in_compatible_vals)+
    from 2(1) show ?case
      by (cases vp) (auto simp: SubsVals_nonempty IH fun_upd_in_compatible_vals_notin compatible_vals_fun_upd)
  }
next
  case (Prev I \<phi>)
  {
    case 1
    with Prev[of vs] show ?case
      by (cases sp) auto
  next
    case 2
    with Prev[of vs] show ?case
      by (cases vp) auto
  }
next
  case (Next I \<phi>)
  {
    case 1
    with Next[of vs] show ?case
      by (cases sp) (auto simp: Let_def)
  next
    case 2
    with Next[of vs] show ?case
      by (cases vp) auto
  }
next
  case (Once I \<phi>)
  {
    case 1
    with Once[of vs] show ?case
      by (cases sp) (auto simp: Let_def)
  next
    case 2
    with Once[of vs] show ?case
      by (cases vp) auto
  }
next
  case (Historically I \<phi>)
  {
    case 1
    with Historically[of vs] show ?case
      by (cases sp) auto
  next
    case 2
    with Historically[of vs] show ?case
      by (cases vp) (auto simp: Let_def)
  }
next
  case (Eventually I \<phi>)
  {
    case 1
    with Eventually[of vs] show ?case
      by (cases sp) (auto simp: Let_def)
  next
    case 2
    with Eventually[of vs] show ?case
      by (cases vp) auto
  }
next
  case (Always I \<phi>)
  {
    case 1
    with Always[of vs] show ?case
      by (cases sp) auto
  next
    case 2
    with Always[of vs] show ?case
      by (cases vp) (auto simp: Let_def)
  }
next
  case (Since \<phi>1 I \<phi>2)
  {
    case 1
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 1(1) show ?case
    proof (cases sp)
      case (SSince sp' sps)
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SSince s_check_exec_simps s_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set sps"]
          Since(1)[OF comp_fv(1) 1(2)] Since(3)[OF comp_fv(2) 1(2), of sp'] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set sps", OF refl])
             apply (metis 1(1) equals0I fv.simps(17))
            apply (metis 1(1) equals0I fv.simps(17))
           apply (metis 1(1) equals0I fv.simps(17))
          apply (metis 1(1) equals0I fv.simps(17))
         apply (metis (mono_tags, lifting) 1(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        subgoal for sp
          using check_fv_cong(1)[of \<phi>1 _ _ sp]
          apply (metis (mono_tags, lifting) 1(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
          done
        done
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 2(1) show ?case
    proof (cases vp)
      case (VSince i vp' vps)
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding VSince v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Since(2)[OF comp_fv(1) 2(2), of vp'] Since(4)[OF comp_fv(2) 2(2)] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl])
             apply (metis 2(1) equals0I fv.simps(17))
            apply (metis 2(1) equals0I fv.simps(17))
           apply (metis 2(1) equals0I fv.simps(17))
          apply (metis 2(1) equals0I fv.simps(17))
         apply (metis (mono_tags, lifting) 2(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        subgoal for vp
          using check_fv_cong(2)[of \<phi>2 _ _ vp]
          apply (metis (mono_tags, lifting) 2(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
          done
        done
    next
      case (VSinceInf i j vps)
      show ?thesis
        unfolding VSinceInf v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Since(4)[OF comp_fv(2) 2(2)] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl])
           apply (metis 2(1) equals0I fv.simps(17))
          apply (metis 2(1) equals0I fv.simps(17))
         apply (metis 2(1) equals0I fv.simps(17))
        subgoal for vp
          using check_fv_cong(2)[of \<phi>2 _ _ vp]
          apply (metis (mono_tags, lifting) 2(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
          done
        done
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (Until \<phi>1 I \<phi>2)
  {
    case 1
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 1(1) show ?case
    proof (cases sp)
      case (SUntil sps sp')
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SUntil s_check_exec_simps s_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set sps"]
          Until(1)[OF comp_fv(1) 1(2)] Until(3)[OF comp_fv(2) 1(2), of sp'] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set sps", OF refl])
             apply (metis 1(1) equals0I fv.simps(18))
            apply (metis 1(1) equals0I fv.simps(18))
           apply (metis 1(1) equals0I fv.simps(18))
          apply (metis 1(1) equals0I fv.simps(18))
         apply (metis (mono_tags, lifting) 1(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        subgoal for sp
          using check_fv_cong(1)[of \<phi>1 _ _ sp]
          apply (metis (mono_tags, lifting) 1(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
          done
        done
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    then have comp_fv: "compatible_vals (fv \<phi>1) vs \<noteq> {}" "compatible_vals (fv \<phi>2) vs \<noteq> {}"
      by (auto simp: compatible_vals_union_eq)
    from 2(1) show ?case
    proof (cases vp)
      case (VUntil i vps vp')
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding VUntil v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Until(2)[OF comp_fv(1) 2(2), of vp'] Until(4)[OF comp_fv(2) 2(2)] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl])
             apply (metis 2(1) equals0I fv.simps(18))
            apply (metis 2(1) equals0I fv.simps(18))
           apply (metis 2(1) equals0I fv.simps(18))
         apply (metis (mono_tags, lifting) 2(2) IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        subgoal for vp
          using check_fv_cong(2)[of \<phi>2 _ _ vp]
          apply (metis (mono_tags, lifting) 2(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
          done
        done
    next
      case (VUntilInf i j vps)
      show ?thesis
        unfolding VUntilInf v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Until(4)[OF comp_fv(2) 2(2)] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl])
           apply (metis 2(1) equals0I fv.simps(18))
          apply (metis 2(1) equals0I fv.simps(18))
         apply (metis 2(1) equals0I fv.simps(18))
        subgoal for vp
          using check_fv_cong(2)[of \<phi>2 _ _ vp]
          apply (metis (mono_tags, lifting) 2(2) IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
          done
        done
    qed (auto simp: compatible_vals_union_eq)
  }
qed

lemma s_check_code[code]: "s_check v \<phi> sp = s_check_exec (\<lambda>x. {v x}) \<phi> sp"
  by (subst check_exec_check)
    (auto simp: compatible_vals_def elim: check_fv_cong[THEN iffD2, rotated])

lemma v_check_code[code]: "v_check v \<phi> vp = v_check_exec (\<lambda>x. {v x}) \<phi> vp"
  by (subst check_exec_check)
    (auto simp: compatible_vals_def elim: check_fv_cong[THEN iffD2, rotated])

lift_definition trivial_part :: "'pt \<Rightarrow> ('d, 'pt) part" is "\<lambda>pt. [(UNIV, pt)]"
  by (simp add: partition_on_space)

lemma part_hd_trivial[simp]: "part_hd (trivial_part pt) = pt"
  unfolding part_hd_def
  by (transfer) simp

lemma SubsVals_trivial[simp]: "SubsVals (trivial_part pt) = {(UNIV, pt)}"
  unfolding SubsVals_def
  by (transfer) simp

lemma 
  assumes "VIO \<sigma> (v(x := z)) i \<phi>" 
  shows "MFOTL.future_bounded \<phi> \<longrightarrow> (\<exists>vp. v_at vp = i \<and> local.v_check (v(x := z)) \<phi> vp) \<Longrightarrow> MFOTL.future_bounded \<phi>"
  apply auto
  oops

lemma check_AD_cong:
  assumes "(\<forall>x \<in> MFOTL.fv \<phi>. v1 x = v2 x \<or> v1 x \<notin> AD \<phi> i \<and> v2 x \<notin> AD \<phi> i)"
  shows "(s_at sp = i \<Longrightarrow> s_check v1 \<phi> sp \<longleftrightarrow> s_check v2 \<phi> sp)"
        "(v_at vp = i \<Longrightarrow> v_check v1 \<phi> vp \<longleftrightarrow> v_check v2 \<phi> vp)"
  using assms
proof (induction v1 \<phi> sp and v1 \<phi> vp rule: s_check_v_check.induct)
  case (1 v f p)
  thm 1(1-23)[OF refl]
  show ?case
  proof (cases p)
    case (SPred i P ts)
    then show ?thesis
      using 1(25)
      apply (cases f; clarsimp simp:)
      subgoal for P' ts'
        using eval_trms_fv_cong[of ts' v v2]
        using val_notin_AD_iff[THEN iffD1, rule_format, of _ "P' \<dagger> ts'", simplified]
        apply auto
        sorry
      sorry
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

unbundle MFOTL_no_notation \<comment> \<open> disable notation \<close>

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
  then show ?case 
    apply simp
    apply (rule exI[of _ "SPred i r ts"])
    apply (simp add: fun_upd_def)
    done
next
  case (VPred r v ts i)
  then show ?case 
    apply simp
    apply (rule exI[of _ "VPred i r ts"])
    apply (simp add: fun_upd_def)
    done
next
  case (SNeg v i \<phi>)
  then show ?case 
    apply clarsimp
    subgoal for vp
      apply (rule exI[of _ "SNeg vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VNeg v i \<phi>)
  then show ?case 
    apply clarsimp
    subgoal for sp
      apply (rule exI[of _ "VNeg sp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (SOrL v i \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    subgoal for sp
      apply (rule exI[of _ "SOrL sp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (SOrR v i \<psi> \<phi>)
  then show ?case 
    apply clarsimp
    subgoal for sp
      apply (rule exI[of _ "SOrR sp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VOr v i \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    subgoal for vp1 vp2
      apply (rule exI[of _ "VOr vp1 vp2"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (SAnd v i \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    subgoal for sp1 sp2
      apply (rule exI[of _ "SAnd sp1 sp2"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VAndL v i \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    subgoal for vp
      apply (rule exI[of _ "VAndL vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VAndR v i \<psi> \<phi>)
  then show ?case 
    apply clarsimp
    subgoal for vp
      apply (rule exI[of _ "VAndR vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (SImpL v i \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    subgoal for vp
      apply (rule exI[of _ "SImpL vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (SImpR v i \<psi> \<phi>)
  then show ?case
    apply clarsimp
    subgoal for sp
      apply (rule exI[of _ "SImpR sp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VImp v i \<phi> \<psi>)
  then show ?case
    apply clarsimp
    subgoal for sp vp
      apply (rule exI[of _ "VImp sp vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (SIffSS v i \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    subgoal for sp vp
      apply (rule exI[of _ "SIffSS sp vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (SIffVV v i \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    subgoal for vp1 vp2
      apply (rule exI[of _ "SIffVV vp1 vp2"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VIffSV v i \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    subgoal for sp vp
      apply (rule exI[of _ "VIffSV sp vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VIffVS v i \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    subgoal for vp sp
      apply (rule exI[of _ "VIffVS vp sp"])
      apply (simp add: fun_upd_def)
      done
    done
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
  case (VExists v x i \<phi>)
  from VExists have fb: "MFOTL.future_bounded \<phi>"
    apply (rule allE[of _ z "MFOTL.future_bounded \<phi>"])
    apply (erule conjE[OF _ _])
    sorry
  obtain mypick where mypick_def: "v_at (mypick z) = i \<and> v_check (v(x:=z)) \<phi> (mypick z)" for z
    apply (atomize_elim)
    apply (rule choice)
    using VExists fb apply (cases \<phi>, simp_all)
    done 
  define mypart where "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> (AD \<phi> i)))"
  have mypick_at: "v_at (mypick (SOME z. z \<notin> local.AD \<phi> i)) = i"
    by (simp add: mypick_def)
  have v_at_myp: "v_at (VExists x mypart) = i"
    using part_hd_tabulate[of \<phi> mypick i, OF fb mypick_at]
    by (simp add: mypart_def) 
  have v_check_myp: "v_check v (MFOTL.Exists x \<phi>) (VExists x mypart)"
    sorry 
  show ?case using v_at_myp v_check_myp by blast
next
  case (SForall v x i \<phi>)
  then show ?case sorry
next
  case (VForall v x i \<phi>)
  then show ?case 
    apply clarsimp
    subgoal for z vp
      apply (rule exI[of _ "VForall x z vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (SPrev i I v \<phi>)
  then show ?case 
    apply clarsimp
    subgoal for sp
      apply (rule exI[of _ "SPrev sp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VPrev i v \<phi> I)
  then show ?case 
    apply clarsimp
    subgoal for vp
      apply (rule exI[of _ "VPrev vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VPrevZ i v I \<phi>)
  then show ?case
    apply clarsimp
    apply (rule exI[of _ "VPrevZ"])
    apply (simp add: fun_upd_def)
    done
next
  case (VPrevOutL i I v \<phi>)
  then show ?case
    apply clarsimp
    apply (rule exI[of _ "VPrevOutL i"])
    apply (simp add: fun_upd_def)
    done
next
  case (VPrevOutR i I v \<phi>)
  then show ?case 
    apply clarsimp
    apply (rule exI[of _ "VPrevOutR i"])
    apply (simp add: fun_upd_def)
    done
next
  case (SNext i I v \<phi>)
  then show ?case 
    apply clarsimp
    subgoal for sp
      apply (rule exI[of _ "SNext sp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VNext v i \<phi> I)
  then show ?case 
    apply clarsimp
    subgoal for vp
      apply (rule exI[of _ "VNext vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VNextOutL i I v \<phi>)
  then show ?case 
    apply clarsimp
    apply (rule exI[of _ "VNextOutL i"])
    apply (simp add: fun_upd_def)
    done
next
  case (VNextOutR i I v \<phi>)
  then show ?case 
    apply clarsimp
    apply (rule exI[of _ "VNextOutR i"])
    apply (simp add: fun_upd_def)
    done
next
  case (SOnce j i I v \<phi>)
  then show ?case 
    apply clarsimp
    subgoal for sp
      apply (rule exI[of _ "SOnce i sp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VOnceOut i I v \<phi>)
  then show ?case 
    apply clarsimp
    apply (rule exI[of _ "VOnceOut i"])
    apply (simp add: fun_upd_def)
    done
next
  case (VOnce j I i v \<phi>)
  then show ?case sorry
next
  case (SEventually j i I v \<phi>)
  then show ?case 
    apply clarsimp
    subgoal for j sp
      apply (rule exI[of _ "SEventually i sp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (VEventually I i v \<phi>)
  then show ?case sorry
next
  case (SHistorically j I i v \<phi>)
  then show ?case sorry
next
  case (SHistoricallyOut i I v \<phi>)
  then show ?case 
    apply clarsimp
    apply (rule exI[of _ "SHistoricallyOut i"])
    apply (simp add: fun_upd_def)
    done
next
  case (VHistorically j i I v \<phi>)
  then show ?case 
    apply clarsimp
    subgoal for vp
      apply (rule exI[of _ "VHistorically i vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (SAlways I i v \<phi>)
  then show ?case sorry
next
  case (VAlways j i I v \<phi>)
  then show ?case 
    apply clarsimp
    subgoal for j vp
      apply (rule exI[of _ "VAlways i vp"])
      apply (simp add: fun_upd_def)
      done
    done
next
  case (SSince j i I v \<psi> \<phi>)
  then show ?case sorry
next
  case (VSinceOut i I v \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    apply (rule exI[of _ "VSinceOut i"])
    apply (simp add: fun_upd_def)
    done
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

(* Note: this is only used in the Pred case.                                    *)
(* Based on a set of (partial) functions from variables to values of a domain,  *)
(* we compute values for each one of the variables in vars, put them in a list, *)
(* and we create a partition with subsets considering each one of these values  *)
(* and another subset considering the complement of the union of these values.  *)
fun pdt_of :: "nat \<Rightarrow> MFOTL.name \<Rightarrow> 'd MFOTL.trm list \<Rightarrow> MFOTL.name list \<Rightarrow> (MFOTL.name \<rightharpoonup> 'd) set \<Rightarrow> 'd expl" where
  "pdt_of i r ts [] V = (if Set.is_empty V then Leaf (Inr (VPred i r ts)) else Leaf (Inl (SPred i r ts)))"
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
  (pdt_of i r ts (filter (\<lambda>x. x \<in> MFOTL.fv (MFOTL.Pred r ts)) vars) (Option.these (match ts ` snd ` {rd \<in> \<Gamma> \<sigma> i. fst rd = r })))"
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