(*<*)
theory Checker
  imports Proof_System "HOL-Library.Simps_Case_Conv"
begin
(*>*)

lemma Cons_eq_upt_conv: "x # xs = [m ..< n] \<longleftrightarrow> m < n \<and> x = m \<and> xs = [Suc m ..< n]"
  by (induct n arbitrary: xs) (force simp: Cons_eq_append_conv)+

lemma map_setE[elim_format]: "map f xs = ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> \<exists>x\<in>set xs. f x = y"
  by (induct xs arbitrary: ys) auto

context fixes \<sigma> :: "'d :: {default, linorder} Formula.trace"

begin

fun s_check :: "'d Formula.env \<Rightarrow> 'd Formula.formula \<Rightarrow> 'd sproof \<Rightarrow> bool"
  and v_check :: "'d Formula.env \<Rightarrow> 'd Formula.formula \<Rightarrow> 'd vproof \<Rightarrow> bool" where
  "s_check v f p = (case (f, p) of
    (Formula.TT, STT i) \<Rightarrow> True
  | (Formula.Pred r ts, SPred i s ts') \<Rightarrow> 
    (r = s \<and> ts = ts' \<and> (r, Formula.eval_trms v ts) \<in> \<Gamma> \<sigma> i)
  | (Formula.Eq_Const x c, SEq_Const i x' c') \<Rightarrow>
    (c = c' \<and> x = x' \<and> v x = c)
  | (Formula.Neg \<phi>, SNeg vp) \<Rightarrow> v_check v \<phi> vp
  | (Formula.Or \<phi> \<psi>, SOrL sp1) \<Rightarrow> s_check v \<phi> sp1
  | (Formula.Or \<phi> \<psi>, SOrR sp2) \<Rightarrow> s_check v \<psi> sp2
  | (Formula.And \<phi> \<psi>, SAnd sp1 sp2) \<Rightarrow> s_check v \<phi> sp1 \<and> s_check v \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (Formula.Imp \<phi> \<psi>, SImpL vp1) \<Rightarrow> v_check v \<phi> vp1
  | (Formula.Imp \<phi> \<psi>, SImpR sp2) \<Rightarrow> s_check v \<psi> sp2
  | (Formula.Iff \<phi> \<psi>, SIffSS sp1 sp2) \<Rightarrow> s_check v \<phi> sp1 \<and> s_check v \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (Formula.Iff \<phi> \<psi>, SIffVV vp1 vp2) \<Rightarrow> v_check v \<phi> vp1 \<and> v_check v \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (Formula.Exists x \<phi>, SExists y val sp) \<Rightarrow> (x = y \<and> s_check (v (x := val)) \<phi> sp)
  | (Formula.Forall x \<phi>, SForall y sp_part) \<Rightarrow> (let i = s_at (part_hd sp_part)
      in x = y \<and> (\<forall>(sub, sp) \<in> SubsVals sp_part. s_at sp = i \<and> (\<forall>z \<in> sub. s_check (v (x := z)) \<phi> sp)))
  | (Formula.Prev I \<phi>, SPrev sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SPrev sp) in 
    i = j+1 \<and> mem (\<Delta> \<sigma> i) I \<and> s_check v \<phi> sp)
  | (Formula.Next I \<phi>, SNext sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SNext sp) in
    j = i+1 \<and> mem (\<Delta> \<sigma> j) I \<and> s_check v \<phi> sp)
  | (Formula.Once I \<phi>, SOnce i sp) \<Rightarrow> 
    (let j = s_at sp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> s_check v \<phi> sp)
  | (Formula.Eventually I \<phi>, SEventually i sp) \<Rightarrow> 
    (let j = s_at sp in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> s_check v \<phi> sp)
  | (Formula.Historically I \<phi>, SHistoricallyOut i) \<Rightarrow> 
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (Formula.Historically I \<phi>, SHistorically i li sps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - b))
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map s_at sps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>sp \<in> set sps. s_check v \<phi> sp))
  | (Formula.Always I \<phi>, SAlways i hi sps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) 
    \<and> right I \<noteq> \<infinity>
    \<and> map s_at sps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>sp \<in> set sps. s_check v \<phi> sp))
  | (Formula.Since \<phi> I \<psi>, SSince sp2 sp1s) \<Rightarrow>
    (let i = s_at (SSince sp2 sp1s); j = s_at sp2 in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I 
    \<and> map s_at sp1s = [j+1 ..< i+1] 
    \<and> s_check v \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check v \<phi> sp1))
  | (Formula.Until \<phi> I \<psi>, SUntil sp1s sp2) \<Rightarrow>
    (let i = s_at (SUntil sp1s sp2); j = s_at sp2 in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I
    \<and> map s_at sp1s = [i ..< j] \<and> s_check v \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check v \<phi> sp1))
  | ( _ , _) \<Rightarrow> False)"
| "v_check v f p = (case (f, p) of
    (Formula.FF, VFF i) \<Rightarrow> True
  | (Formula.Pred r ts, VPred i pred ts') \<Rightarrow> 
    (r = pred \<and> ts = ts' \<and> (r, Formula.eval_trms v ts) \<notin> \<Gamma> \<sigma> i)
  | (Formula.Eq_Const x c, VEq_Const i x' c') \<Rightarrow>
    (c = c' \<and> x = x' \<and> v x \<noteq> c)
  | (Formula.Neg \<phi>, VNeg sp) \<Rightarrow> s_check v \<phi> sp
  | (Formula.Or \<phi> \<psi>, VOr vp1 vp2) \<Rightarrow> v_check v \<phi> vp1 \<and> v_check v \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (Formula.And \<phi> \<psi>, VAndL vp1) \<Rightarrow> v_check v \<phi> vp1
  | (Formula.And \<phi> \<psi>, VAndR vp2) \<Rightarrow> v_check v \<psi> vp2
  | (Formula.Imp \<phi> \<psi>, VImp sp1 vp2) \<Rightarrow> s_check v \<phi> sp1 \<and> v_check v \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (Formula.Iff \<phi> \<psi>, VIffSV sp1 vp2) \<Rightarrow> s_check v \<phi> sp1 \<and> v_check v \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (Formula.Iff \<phi> \<psi>, VIffVS vp1 sp2) \<Rightarrow> v_check v \<phi> vp1 \<and> s_check v \<psi> sp2 \<and> v_at vp1 = s_at sp2
  | (Formula.Exists x \<phi>, VExists y vp_part) \<Rightarrow> (let i = v_at (part_hd vp_part)
      in x = y \<and> (\<forall>(sub, vp) \<in> SubsVals vp_part. v_at vp = i \<and> (\<forall>z \<in> sub. v_check (v (x := z)) \<phi> vp)))
  | (Formula.Forall x \<phi>, VForall y val vp) \<Rightarrow> (x = y \<and> v_check (v (x := val)) \<phi> vp)
  | (Formula.Prev I \<phi>, VPrev vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VPrev vp) in
    i = j+1 \<and> v_check v \<phi> vp)
  | (Formula.Prev I \<phi>, VPrevZ) \<Rightarrow>
    v_at (VPrevZ::'d vproof) = 0
  | (Formula.Prev I \<phi>, VPrevOutL i) \<Rightarrow>
    i > 0 \<and> \<Delta> \<sigma> i < left I
  | (Formula.Prev I \<phi>, VPrevOutR i) \<Rightarrow>
    i > 0 \<and> enat (\<Delta> \<sigma> i) > right I
  | (Formula.Next I \<phi>, VNext vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VNext vp) in
    j = i+1 \<and> v_check v \<phi> vp)
  | (Formula.Next I \<phi>, VNextOutL i) \<Rightarrow>
    \<Delta> \<sigma> (i+1) < left I
  | (Formula.Next I \<phi>, VNextOutR i) \<Rightarrow>
    enat (\<Delta> \<sigma> (i+1)) > right I
  | (Formula.Once I \<phi>, VOnceOut i) \<Rightarrow> 
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (Formula.Once I \<phi>, VOnce i li vps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp \<in> set vps. v_check v \<phi> vp))
  | (Formula.Eventually I \<phi>, VEventually i hi vps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>vp \<in> set vps. v_check v \<phi> vp))
  | (Formula.Historically I \<phi>, VHistorically i vp) \<Rightarrow> 
    (let j = v_at vp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> v_check v \<phi> vp)
  | (Formula.Always I \<phi>, VAlways i vp) \<Rightarrow> 
    (let j = v_at vp
    in j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> v_check v \<phi> vp)
  | (Formula.Since \<phi> I \<psi>, VSinceOut i) \<Rightarrow>
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (Formula.Since \<phi> I \<psi>, VSince i vp1 vp2s) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> ETP_p \<sigma> i b \<le> j) \<and> j \<le> i
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [j ..< (LTP_p \<sigma> i I) + 1] \<and> v_check v \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | (Formula.Since \<phi> I \<psi>, VSinceInf i li vp2s) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | (Formula.Until \<phi> I \<psi>, VUntil i vp2s vp1) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> j < LTP_f \<sigma> i b) \<and> i \<le> j
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< j + 1] \<and> v_check v \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | (Formula.Until \<phi> I \<psi>, VUntilInf i hi vp2s) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< hi + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check v \<psi> vp2))
  | ( _ , _) \<Rightarrow> False)"


declare s_check.simps[simp del] v_check.simps[simp del]
simps_of_case s_check_simps[simp]: s_check.simps[unfolded prod.case] (splits: Formula.formula.split sproof.split)
simps_of_case v_check_simps[simp]: v_check.simps[unfolded prod.case] (splits: Formula.formula.split vproof.split)


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
  case SEq_Const
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.SEq_Const)
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
  case VEq_Const
  then show ?case by (cases \<phi>) (auto intro: SAT_VIO.VEq_Const)
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

lemma set_positions_eq: "set (positions xs x) = {n. xs ! n = x \<and> n < length xs}"
  apply (induct xs arbitrary: x)
  using less_Suc_eq_0_disj
  by (auto simp: positions_eq_nil_iff[symmetric] image_iff split: if_splits)

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

primrec mk_values :: "('b Formula.trm \<times> 'a set) list \<Rightarrow> 'a list set" 
  where "mk_values [] = {[]}" 
  | "mk_values (T # Ts) = (case T of 
      (Formula.Var x, X) \<Rightarrow> 
        let terms = map fst Ts in
        if Formula.Var x \<in> set terms then
          let fst_pos = hd (positions terms (Formula.Var x)) in (\<lambda>xs. (xs ! fst_pos) # xs) ` (mk_values Ts)
        else set_Cons X (mk_values Ts)
    | (Formula.Const a, X) \<Rightarrow> set_Cons X (mk_values Ts))"

lemma mk_values_nempty: 
  "{} \<notin> set (map snd tXs) \<Longrightarrow> mk_values tXs \<noteq> {}"
  by (induct tXs)
    (auto simp: set_Cons_def image_iff split: Formula.trm.splits if_splits)

lemma mk_values_not_Nil: 
  "{} \<notin> set (map snd tXs) \<Longrightarrow> tXs \<noteq> [] \<Longrightarrow> vs \<in> mk_values tXs \<Longrightarrow> vs \<noteq> []"
  by (induct tXs)
    (auto simp: set_Cons_def image_iff split: Formula.trm.splits if_splits)

lemma mk_values_nth_cong: "Formula.Var x \<in> set (map fst tXs) 
  \<Longrightarrow> n \<in> set (positions (map fst tXs) (Formula.Var x))
  \<Longrightarrow> m \<in> set (positions (map fst tXs) (Formula.Var x))
  \<Longrightarrow> vs \<in> mk_values tXs
  \<Longrightarrow> vs ! n = vs ! m"
  apply (induct tXs arbitrary: n m vs x)
   apply simp
  subgoal for tX tXs n m v x
    apply (cases "fst tX = Formula.Var x"; cases "Formula.Var x \<in> set (map fst tXs)")
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
      apply (clarsimp simp: image_iff set_Cons_def split: Formula.trm.splits)
      by (split if_splits; simp add: image_iff set_Cons_def)
        (metis fst_conv nth_Cons_Suc)+
    by clarsimp
  done

unbundle MFOTL_notation \<comment> \<open> enable notation \<close>

(* text \<open> OBS: Even if there is an infinite set for @{term "\<^bold>v x"}, we can still get a 
 finite @{term mk_values} because it only cares about the latest set in the list
 for @{term "\<^bold>v ''x''"}. This is why the definition below has many cases. \<close> *)

(* term "''P'' \<dagger> [\<^bold>c (0::nat), \<^bold>v ''x'', \<^bold>v ''y'']"
value "mk_values [(\<^bold>c (0::nat), {0}), (\<^bold>v ''x'', Complement {0::nat, 1}), (\<^bold>v ''y'', {0::nat, 1}), (\<^bold>v ''x'', {0::nat, 1})]" *)

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

lemma infinite_mk_values1: "\<forall>tX \<in> set tXs. snd tX \<noteq> {} \<Longrightarrow> tY \<in> set tXs 
  \<Longrightarrow> \<forall>Y. (fst tY, Y) \<in> set tXs \<longrightarrow> infinite Y \<Longrightarrow> infinite (mk_values tXs)"
proof (induct tXs arbitrary: tY)
  case (Cons tX tXs)
  show ?case
  proof (auto simp add: Let_def image_iff split: prod.splits trm.splits,
      goal_cases var_in var_out const)
    case (var_in X x Y)
    hence "\<forall>tX\<in>set tXs. snd tX \<noteq> {}"
      by (simp add: Cons.prems(1))
    moreover have "\<forall>Z. (trm.Var x, Z) \<in> set tXs \<longrightarrow> infinite Z"
      using Cons.prems(2,3) var_in
      by (cases "tY \<in> set tXs"; clarsimp)
        (metis (no_types, lifting) Cons.hyps Cons.prems(1)
            finite_imageD inj_on_def list.inject list.set_intros(2))
    ultimately have "infinite (mk_values tXs)"
      using Cons.hyps[OF _ \<open>(trm.Var x, Y) \<in> set tXs\<close>]
      by auto
    moreover have "inj (\<lambda>xs. xs ! hd (positions (map fst tXs) (trm.Var x)) # xs)"
      by (clarsimp simp: inj_on_def)
    ultimately show ?case
      using var_in(3) finite_imageD inj_on_subset 
      by fastforce
  next
    case (var_out Y x)
    hence "infinite Y"
      using Cons.prems
      by (metis Cons.hyps fst_conv infinite_set_ConsI(2) 
          insert_iff list.simps(15) snd_conv)
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
      by (metis Cons.hyps fst_conv infinite_set_ConsI(2) 
          insert_iff list.simps(15) snd_conv)
    moreover have "mk_values tXs \<noteq> {}"
      using Cons.prems 
      by (auto intro!: mk_values_nemptyI)
    then show ?case
      using Cons const infinite_set_ConsI(1)[OF \<open>mk_values tXs \<noteq> {}\<close> \<open>infinite Y\<close>]
      by auto
  qed
qed simp

lemma subset_positions_map_fst: "set (positions tXs tX) \<subseteq> set (positions (map fst tXs) (fst tX))"
  by (induct tXs arbitrary: tX)
    (auto simp: subset_eq)

lemma subset_positions_map_snd: "set (positions tXs tX) \<subseteq> set (positions (map snd tXs) (snd tX))"
  by (induct tXs arbitrary: tX)
    (auto simp: subset_eq)

lemma Max_eqI: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> a \<le> b) \<Longrightarrow> \<exists>a\<in>A. b \<le> a \<Longrightarrow> Max A = b"
  by (rule antisym[OF Max.boundedI Max_ge_iff[THEN iffD2]]; clarsimp)

lemma Max_Suc: "X \<noteq> {} \<Longrightarrow> finite X \<Longrightarrow> Max (Suc ` X) = Suc (Max X)"
  apply (rule Max_eqI; clarsimp)
  using Max_ge Max_in by blast

lemma Max_insert0: "X \<noteq> {} \<Longrightarrow> finite X \<Longrightarrow> Max (insert (0::nat) X) = Max X"
  apply (rule Max_eqI; clarsimp)
  using Max_ge Max_in by blast+

lemma positions_Cons_notin_tail: "x \<notin> set xs \<Longrightarrow> positions (x # xs) x = [0::nat]"
  by (cases xs) (auto simp: positions_eq_nil_iff)

lemma Max_set_positions_Cons: 
  "x \<notin> set xs \<Longrightarrow> Max (set (positions (x # xs) x)) = 0"
  "y \<in> set xs \<Longrightarrow> Max (set (positions (x # xs) y)) = Suc (Max (set (positions xs y)))"
  apply (subst positions_Cons_notin_tail)
  by simp_all (subst Max_Suc; clarsimp simp: positions_eq_nil_iff)+

lemma infinite_mk_values2: "\<forall>tX\<in>set tXs. snd tX \<noteq> {} 
  \<Longrightarrow> tY \<in> set tXs \<Longrightarrow> infinite (snd tY) 
  \<Longrightarrow> Max (set (positions tXs tY)) \<ge> Max (set (positions (map fst tXs) (fst tY)))
  \<Longrightarrow> infinite (mk_values tXs)"
proof (induct tXs arbitrary: tY)
  case (Cons tX tXs)
  hence obs1: "\<forall>tX\<in>set tXs. snd tX \<noteq> {}"
    by (simp add: Cons.prems(1))
  note IH = Cons.hyps[OF obs1 _ \<open>infinite (snd tY)\<close>]
  have obs2: "tY \<in> set tXs 
    \<Longrightarrow> Max (set (positions (map fst tXs) (fst tY))) \<le> Max (set (positions tXs tY))"
    using Cons.prems(4)
    apply (simp only: list.map(2))
    by (subst (asm) Max_set_positions_Cons, simp)+
      linarith
  show ?case
  proof (auto simp add: Let_def image_iff split: prod.splits trm.splits,
      goal_cases var_in var_out const)
    case (var_in X x Y)
    then show ?case
    proof (cases "tY \<in> set tXs")
      case True
      hence "infinite ((\<lambda>Xs. Xs ! hd (positions (map fst tXs) (trm.Var x)) # Xs) ` mk_values tXs)"
        using IH[OF True obs2[OF True]] finite_imageD inj_on_def by blast
      then show "False"
        using var_in by blast
    next
      case False
      have "Max (set (positions (map fst (tX # tXs)) (fst tY))) 
      = Suc (Max (set (positions (map fst tXs) (fst tY))))"
        using Cons.prems var_in
        by (simp only: list.map(2))
          (subst Max_set_positions_Cons; force simp: image_iff)
      moreover have "tY \<notin> set tXs \<Longrightarrow> Max (set (positions (tX # tXs) tY)) = (0::nat)"
        using Cons.prems Max_set_positions_Cons(1) by fastforce
      ultimately show "False"
        using Cons.prems(4) False
        by linarith 
    qed
  next
    case (var_out X x)
    then show ?case
    proof (cases "tY \<in> set tXs")
      case True
      hence "infinite (mk_values tXs)"
        using IH obs2 by blast
      hence "infinite (set_Cons X (mk_values tXs))"
        by (metis Cons.prems(1) infinite_set_ConsI(2) list.set_intros(1) snd_conv var_out(2))
      then show "False"
        using var_out by blast
    next
      case False
      hence "snd tY = X" and "infinite X"
        using var_out Cons.prems
        by auto
      hence "infinite (set_Cons X (mk_values tXs))"
        by (simp add: infinite_set_ConsI(1) mk_values_nemptyI obs1)
      then show "False"
        using var_out by blast
    qed
  next
    case (const Y c)
    then show ?case
    proof (cases "tY \<in> set tXs")
      case True
      hence "infinite (mk_values tXs)"
        using IH obs2 by blast
      hence "infinite (set_Cons Y (mk_values tXs))"
        by (metis Cons.prems(1) const(1) infinite_set_ConsI(2) list.set_intros(1) snd_conv)
      then show "False"
        using const by blast
    next
      case False
      hence "infinite (set_Cons Y (mk_values tXs))"
        using const Cons.prems
        by (simp add: infinite_set_ConsI(1) mk_values_nemptyI obs1)
      then show "False"
        using const by blast
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
    and ex_dupl_inf: "\<not> list_all (\<lambda>tX. Max (set (positions tXs tX)) 
    < Max (set (positions (map fst tXs) (fst tX))))
        (filter (\<lambda>x. infinite (snd x) \<and> (\<exists>b. (fst x, b) \<in> set tXs \<and> finite b)) tXs)" 
    and filter: "filter (\<lambda>x. infinite (snd x)) tXs \<noteq> []"
  then obtain tY and Z where "tY \<in> set tXs" 
    and "infinite (snd tY)"
    and "(fst tY, Z) \<in> set tXs"
    and "finite Z"
    and "Max (set (positions tXs tY)) \<ge> Max (set (positions (map fst tXs) (fst tY)))"
    by (auto simp: list_all_iff)
  hence "infinite (mk_values tXs)"
    using infinite_mk_values2[OF \<open>\<forall>tX\<in>set tXs. snd tX \<noteq> {}\<close> \<open>tY \<in> set tXs\<close>]
    by auto
  hence "infinite ({p} \<times> mk_values tXs)"
    using finite_cartesian_productD2 by auto
  thus "{p} \<times> mk_values tXs \<subseteq> X \<Longrightarrow> False"
    using \<open>finite X\<close>
    by (simp add: finite_subset)
qed

unbundle MFOTL_notation \<comment> \<open> enable notation \<close>

lemma mk_values_sound: "cs \<in> mk_values (Formula.eval_trms_set vs ts) 
  \<Longrightarrow> \<exists>v\<in>compatible_vals (fv (p \<dagger> ts)) vs. cs = Formula.eval_trms v ts"
proof (induct ts arbitrary: cs vs)
  let ?evals = Formula.eval_trms_set
    and ?eval = "Formula.eval_trm_set"
  case (Cons t ts)
  show ?case
  proof(cases t)
    case (Var x)
    let ?Ts = "?evals vs ts"
    have "?evals vs (t # ts) = (\<^bold>v x, vs x) # ?Ts"
      using Var by (simp add: Formula.eval_trms_set_def)
    show ?thesis
    proof (cases "\<^bold>v x \<in> set ts")
      case True
      then obtain n where n_in: "n \<in> set (positions ts (\<^bold>v x))"
        and nth_n: "ts ! n = \<^bold>v x"
        by (meson fst_pos_in_positions nth_fst_pos)
      hence n_in': "n \<in> set (positions (map fst ?Ts) (\<^bold>v x))"
        by (induct ts arbitrary: n)
          (auto simp: Formula.eval_trms_set_def split: if_splits)
      have key: "\<^bold>v x \<in> set (map fst ?Ts)"
        using True by (induct ts)
          (auto simp: Formula.eval_trms_set_def)
      then obtain a as
        where as_head: "as ! (hd (positions (map fst ?Ts) (\<^bold>v x))) = a"
          and as_tail: "as \<in> mk_values (Formula.eval_trms_set vs ts)" 
          and as_shape: "cs = a # as"
        using Cons(2) 
        by (clarsimp simp add: Formula.eval_trms_set_def Var image_iff)
      obtain v where v_hyps: "v \<in> compatible_vals (fv (p \<dagger> ts)) vs"
        "as = Formula.eval_trms v ts"
        using Cons(1)[OF as_tail] by blast
      hence as'_nth: "as ! n = v x"
        using nth_n positions_length[OF n_in]
        by (simp add: Formula.eval_trms_def)
      have evals_neq_Nil: "?evals vs ts \<noteq> []"
        using key by auto
      moreover have "positions (map fst (Formula.eval_trms_set vs ts)) (\<^bold>v x) \<noteq> []"
        using positions_eq_nil_iff[of "map fst ?Ts" "\<^bold>v x"] key
        by fastforce
      ultimately have as_hyp: "a = as ! n"
        using mk_values_nth_cong[OF key hd_in_set n_in' as_tail] as_head  by blast
      thus ?thesis
        using Var as_shape True v_hyps as'_nth
        by (auto simp: compatible_vals_def Formula.eval_trms_def intro!: exI[of _ v])
    next
      case False
      hence "\<^bold>v x \<notin> set (map fst ?Ts)"
        using Var
        apply (induct ts arbitrary: x)
        by (auto simp: Formula.eval_trms_set_def image_iff)
          (metis eq_fst_iff eval_trm_set.simps(1) eval_trm_set.simps(2) trm.exhaust)
      then show ?thesis 
        using Cons(2) Var False
        apply (clarsimp simp: Formula.eval_trms_set_def set_Cons_def 
          Formula.eval_trms_def compatible_vals_def split: )
        subgoal for a as
          using Cons(1)[of as vs] 
          apply (clarsimp simp: Formula.eval_trms_set_def Formula.eval_trms_def compatible_vals_def)
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
      by (auto simp: Formula.eval_trms_set_def set_Cons_def 
          Formula.eval_trms_def compatible_def)
  qed
qed (simp add: Formula.eval_trms_set_def Formula.eval_trms_def compatible_vals_def)

lemma fst_eval_trm_set[simp]: 
  "fst (Formula.eval_trm_set vs t) = t"
  by (cases t; clarsimp)

lemma map_fst_eval_trm_set [simp]:
  "map (fst \<circ> Formula.eval_trm_set vs) ts = ts"
  by (induct ts arbitrary: vs) auto

lemma mk_values_complete: "cs = Formula.eval_trms v ts 
  \<Longrightarrow> v \<in> compatible_vals (fv (p \<dagger> ts)) vs
  \<Longrightarrow> cs \<in> mk_values (Formula.eval_trms_set vs ts)"
proof (induct ts arbitrary: v cs vs)
  case (Cons t ts)
  then obtain a as 
    where a_def: "a = Formula.eval_trm v t" 
      and as_def: "as = Formula.eval_trms v ts"
      and cs_cons: "cs = a # as"
    by (auto simp: Formula.eval_trms_def)
  have compat_v_vs: "v \<in> compatible_vals (fv (p \<dagger> (ts))) vs" 
    using Cons.prems
    by (auto simp: compatible_vals_def)
  hence mk_values_ts: "as \<in> mk_values (map (Formula.eval_trm_set vs) ts)"
    using Cons.hyps[OF as_def] 
    unfolding Formula.eval_trms_set_def by blast
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
      hence n_in': "n = hd (positions (map fst (Formula.eval_trms_set vs ts)) (\<^bold>v x))"
        by (clarsimp simp: Formula.eval_trms_set_def)
      moreover have "as ! n = a"
        using a_def as_def nth_n Var n_in True positions_length
        by (fastforce simp: Formula.eval_trms_def)
      moreover have "\<^bold>v x \<in> set (map fst (Formula.eval_trms_set vs ts))"
        using True by (induct ts)
          (auto simp: Formula.eval_trms_set_def)
      ultimately show ?thesis
        using mk_values_ts cs_cons
        by (clarsimp simp: Formula.eval_trms_set_def Var image_iff)
    next
      case False
      then show ?thesis
        using Var cs_cons mk_values_ts Cons.prems a_def
        by (clarsimp simp: Formula.eval_trms_set_def image_iff 
            set_Cons_def compatible_vals_def split: Formula.trm.splits)
    qed
  next
    case (Const a)
    then show ?thesis 
      using cs_cons mk_values_ts Cons.prems a_def
      by (clarsimp simp: Formula.eval_trms_set_def image_iff
            set_Cons_def compatible_vals_def split: Formula.trm.splits)
  qed
qed (simp add: compatible_vals_def 
    Formula.eval_trms_set_def Formula.eval_trms_def)

unbundle MFOTL_no_notation \<comment> \<open> disable notation \<close>

definition "mk_values_subset_Compl r vs ts i = ({r} \<times> mk_values (map (Formula.eval_trm_set vs) ts) \<subseteq> - \<Gamma> \<sigma> i)"

fun check_values where
  "check_values _ _ _ None = None"
| "check_values vs (Formula.Const c # ts) (u # us) f = (if c = u then check_values vs ts us f else None)"
| "check_values vs (Formula.Var x # ts) (u # us) (Some v) = (if u \<in> vs x \<and> (v x = Some u \<or> v x = None) then check_values vs ts us (Some (v(x \<mapsto> u))) else None)"
| "check_values vs [] [] f = f"
| "check_values _ _ _ _ = None"

lemma mk_values_alt:
  "mk_values (Formula.eval_trms_set vs ts) =
   {cs. \<exists>v\<in>compatible_vals (\<Union>(Formula.fv_trm ` set ts)) vs. cs = Formula.eval_trms v ts}"
  by (auto dest!: mk_values_sound intro: mk_values_complete)

lemma check_values_neq_NoneI:
  assumes "v \<in> compatible_vals (\<Union> (Formula.fv_trm ` set ts) - dom f) vs" "\<And>x y. f x = Some y \<Longrightarrow> y \<in> vs x"
  shows "check_values vs ts (Formula.eval_trms (\<lambda>x. case f x of None \<Rightarrow> v x | Some y \<Rightarrow> y) ts) (Some f) \<noteq> None"
  using assms
  apply (induct ts arbitrary: f)
   apply (auto simp: Formula.eval_trms_def)
  apply (case_tac a)
   apply (auto)
  subgoal for ts f x
    apply (drule meta_spec[where x="f"])
    apply (auto simp: domI split: option.splits)
    done
  subgoal for ts f x
    apply (drule meta_spec[where x="f(x \<mapsto> v x)"])
    apply (drule meta_mp)
     apply (auto elim!: compatible_vals_antimono[THEN set_mp, rotated])
    apply (smt (verit, best) eval_trm_fv_cong map_eq_conv option.simps(4) option.simps(5))
    done
  subgoal for ts f x
    apply (auto simp: compatible_vals_def split: option.splits)
    done
  done

lemma check_values_eq_NoneI:
  "\<forall>v\<in>compatible_vals (\<Union> (Formula.fv_trm ` set ts) - dom f) vs. us \<noteq> Formula.eval_trms (\<lambda>x. case f x of None \<Rightarrow> v x | Some y \<Rightarrow> y) ts \<Longrightarrow>
  check_values vs ts us (Some f) = None"
  apply (induct vs ts us "Some f" arbitrary: f rule: check_values.induct)
       apply (auto simp: compatible_vals_def Formula.eval_trms_def)
   apply (erule meta_mp)
  apply safe
  subgoal for vs x ts u us v v'
    apply (drule spec[of _ "v'"])
    apply (auto split: if_splits)
    apply (erule notE)
    apply (rule eval_trm_fv_cong)
    apply (auto split: if_splits option.splits)
    done
    apply (erule meta_mp)
  apply safe
  subgoal for vs x ts u us v v'
    apply (drule spec[of _ "v'(x := u)"])
    apply (auto split: if_splits)
    apply (erule notE)
    apply (rule eval_trm_fv_cong)
    apply (auto split: if_splits option.splits)
    done
  done

lemma mk_values_subset_Compl_code[code]:
  "mk_values_subset_Compl r vs ts i = (\<forall>(q, us) \<in> \<Gamma> \<sigma> i. q \<noteq> r \<or> check_values vs ts us (Some Map.empty) = None)"
  unfolding mk_values_subset_Compl_def Formula.eval_trms_set_def[symmetric] mk_values_alt
  apply (auto simp: subset_eq)
  subgoal for us
    apply (drule spec[of _ us])
    apply (auto simp: check_values_eq_NoneI[where f=Map.empty, simplified])
    done
  subgoal for v
    apply (drule bspec)
     apply assumption
    apply (auto dest: check_values_neq_NoneI[where f=Map.empty, simplified])
    done
  done

fun s_check_exec :: "'d Formula.envset \<Rightarrow> 'd Formula.formula \<Rightarrow> 'd sproof \<Rightarrow> bool"
  and v_check_exec :: "'d Formula.envset \<Rightarrow> 'd Formula.formula \<Rightarrow> 'd vproof \<Rightarrow> bool" where
  "s_check_exec vs f p = (case (f, p) of
    (Formula.TT, STT i) \<Rightarrow> True
  | (Formula.Pred r ts, SPred i s ts') \<Rightarrow> 
    (r = s \<and> ts = ts' \<and> mk_values_subset r (Formula.eval_trms_set vs ts) (\<Gamma> \<sigma> i))
  | (Formula.Eq_Const x c, SEq_Const i x' c') \<Rightarrow> 
    (c = c' \<and> x = x' \<and> vs x = {c})
  | (Formula.Neg \<phi>, SNeg vp) \<Rightarrow> v_check_exec vs \<phi> vp
  | (Formula.Or \<phi> \<psi>, SOrL sp1) \<Rightarrow> s_check_exec vs \<phi> sp1
  | (Formula.Or \<phi> \<psi>, SOrR sp2) \<Rightarrow> s_check_exec vs \<psi> sp2
  | (Formula.And \<phi> \<psi>, SAnd sp1 sp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> s_check_exec vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (Formula.Imp \<phi> \<psi>, SImpL vp1) \<Rightarrow> v_check_exec vs \<phi> vp1
  | (Formula.Imp \<phi> \<psi>, SImpR sp2) \<Rightarrow> s_check_exec vs \<psi> sp2
  | (Formula.Iff \<phi> \<psi>, SIffSS sp1 sp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> s_check_exec vs \<psi> sp2 \<and> s_at sp1 = s_at sp2
  | (Formula.Iff \<phi> \<psi>, SIffVV vp1 vp2) \<Rightarrow> v_check_exec vs \<phi> vp1 \<and> v_check_exec vs \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (Formula.Exists x \<phi>, SExists y val sp) \<Rightarrow> (x = y \<and> s_check_exec (vs (x := {val})) \<phi> sp)
  | (Formula.Forall x \<phi>, SForall y sp_part) \<Rightarrow> (let i = s_at (part_hd sp_part)
      in x = y \<and> (\<forall>(sub, sp) \<in> SubsVals sp_part. s_at sp = i \<and> s_check_exec (vs (x := sub)) \<phi> sp))
  | (Formula.Prev I \<phi>, SPrev sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SPrev sp) in 
    i = j+1 \<and> mem (\<Delta> \<sigma> i) I \<and> s_check_exec vs \<phi> sp)
  | (Formula.Next I \<phi>, SNext sp) \<Rightarrow>
    (let j = s_at sp; i = s_at (SNext sp) in
    j = i+1 \<and> mem (\<Delta> \<sigma> j) I \<and> s_check_exec vs \<phi> sp)
  | (Formula.Once I \<phi>, SOnce i sp) \<Rightarrow> 
    (let j = s_at sp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> s_check_exec vs \<phi> sp)
  | (Formula.Eventually I \<phi>, SEventually i sp) \<Rightarrow> 
    (let j = s_at sp in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> s_check_exec vs \<phi> sp)
  | (Formula.Historically I \<phi>, SHistoricallyOut i) \<Rightarrow> 
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (Formula.Historically I \<phi>, SHistorically i li sps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP \<sigma> (\<tau> \<sigma> i - b))
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map s_at sps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>sp \<in> set sps. s_check_exec vs \<phi> sp))
  | (Formula.Always I \<phi>, SAlways i hi sps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) 
    \<and> right I \<noteq> \<infinity>
    \<and> map s_at sps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>sp \<in> set sps. s_check_exec vs \<phi> sp))
  | (Formula.Since \<phi> I \<psi>, SSince sp2 sp1s) \<Rightarrow>
    (let i = s_at (SSince sp2 sp1s); j = s_at sp2 in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I 
    \<and> map s_at sp1s = [j+1 ..< i+1] 
    \<and> s_check_exec vs \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check_exec vs \<phi> sp1))
  | (Formula.Until \<phi> I \<psi>, SUntil sp1s sp2) \<Rightarrow>
    (let i = s_at (SUntil sp1s sp2); j = s_at sp2 in
    j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I
    \<and> map s_at sp1s = [i ..< j] \<and> s_check_exec vs \<psi> sp2
    \<and> (\<forall>sp1 \<in> set sp1s. s_check_exec vs \<phi> sp1))
  | ( _ , _) \<Rightarrow> False)"
| "v_check_exec vs f p = (case (f, p) of
    (Formula.FF, VFF i) \<Rightarrow> True
  | (Formula.Pred r ts, VPred i pred ts') \<Rightarrow> 
    (r = pred \<and> ts = ts' \<and> mk_values_subset_Compl r vs ts i)
  | (Formula.Eq_Const x c, VEq_Const i x' c') \<Rightarrow> 
    (c = c' \<and> x = x' \<and> c \<notin> vs x)
  | (Formula.Neg \<phi>, VNeg sp) \<Rightarrow> s_check_exec vs \<phi> sp
  | (Formula.Or \<phi> \<psi>, VOr vp1 vp2) \<Rightarrow> v_check_exec vs \<phi> vp1 \<and> v_check_exec vs \<psi> vp2 \<and> v_at vp1 = v_at vp2
  | (Formula.And \<phi> \<psi>, VAndL vp1) \<Rightarrow> v_check_exec vs \<phi> vp1
  | (Formula.And \<phi> \<psi>, VAndR vp2) \<Rightarrow> v_check_exec vs \<psi> vp2
  | (Formula.Imp \<phi> \<psi>, VImp sp1 vp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> v_check_exec vs \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (Formula.Iff \<phi> \<psi>, VIffSV sp1 vp2) \<Rightarrow> s_check_exec vs \<phi> sp1 \<and> v_check_exec vs \<psi> vp2 \<and> s_at sp1 = v_at vp2
  | (Formula.Iff \<phi> \<psi>, VIffVS vp1 sp2) \<Rightarrow> v_check_exec vs \<phi> vp1 \<and> s_check_exec vs \<psi> sp2 \<and> v_at vp1 = s_at sp2
  | (Formula.Exists x \<phi>, VExists y vp_part) \<Rightarrow> (let i = v_at (part_hd vp_part)
      in x = y \<and> (\<forall>(sub, vp) \<in> SubsVals vp_part. v_at vp = i \<and> v_check_exec (vs (x := sub)) \<phi> vp))
  | (Formula.Forall x \<phi>, VForall y val vp) \<Rightarrow> (x = y \<and> v_check_exec (vs (x := {val})) \<phi> vp)
  | (Formula.Prev I \<phi>, VPrev vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VPrev vp) in
    i = j+1 \<and> v_check_exec vs \<phi> vp)
  | (Formula.Prev I \<phi>, VPrevZ) \<Rightarrow>
    v_at (VPrevZ::'d vproof) = 0
  | (Formula.Prev I \<phi>, VPrevOutL i) \<Rightarrow>
    i > 0 \<and> \<Delta> \<sigma> i < left I
  | (Formula.Prev I \<phi>, VPrevOutR i) \<Rightarrow>
    i > 0 \<and> enat (\<Delta> \<sigma> i) > right I
  | (Formula.Next I \<phi>, VNext vp) \<Rightarrow>
    (let j = v_at vp; i = v_at (VNext vp) in
    j = i+1 \<and> v_check_exec vs \<phi> vp)
  | (Formula.Next I \<phi>, VNextOutL i) \<Rightarrow>
    \<Delta> \<sigma> (i+1) < left I
  | (Formula.Next I \<phi>, VNextOutR i) \<Rightarrow>
    enat (\<Delta> \<sigma> (i+1)) > right I
  | (Formula.Once I \<phi>, VOnceOut i) \<Rightarrow> 
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (Formula.Once I \<phi>, VOnce i li vps) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vps = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp \<in> set vps. v_check_exec vs \<phi> vp))
  | (Formula.Eventually I \<phi>, VEventually i hi vps) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vps = [(ETP_f \<sigma> i I) ..< hi + 1]
    \<and> (\<forall>vp \<in> set vps. v_check_exec vs \<phi> vp))
  | (Formula.Historically I \<phi>, VHistorically i vp) \<Rightarrow> 
    (let j = v_at vp in
    j \<le> i \<and> mem (\<tau> \<sigma> i - \<tau> \<sigma> j) I \<and> v_check_exec vs \<phi> vp)
  | (Formula.Always I \<phi>, VAlways i vp) \<Rightarrow> 
    (let j = v_at vp
    in j \<ge> i \<and> mem (\<tau> \<sigma> j - \<tau> \<sigma> i) I \<and> v_check_exec vs \<phi> vp)
  | (Formula.Since \<phi> I \<psi>, VSinceOut i) \<Rightarrow>
    \<tau> \<sigma> i < \<tau> \<sigma> 0 + left I
  | (Formula.Since \<phi> I \<psi>, VSince i vp1 vp2s) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> ETP_p \<sigma> i b \<le> j) \<and> j \<le> i
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [j ..< (LTP_p \<sigma> i I) + 1] \<and> v_check_exec vs \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | (Formula.Since \<phi> I \<psi>, VSinceInf i li vp2s) \<Rightarrow>
    (li = (case right I of \<infinity> \<Rightarrow> 0 | enat b \<Rightarrow> ETP_p \<sigma> i b)
    \<and> \<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i
    \<and> map v_at vp2s = [li ..< (LTP_p \<sigma> i I) + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | (Formula.Until \<phi> I \<psi>, VUntil i vp2s vp1) \<Rightarrow>
    (let j = v_at vp1 in
    (case right I of \<infinity> \<Rightarrow> True | enat b \<Rightarrow> j < LTP_f \<sigma> i b) \<and> i \<le> j
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< j + 1] \<and> v_check_exec vs \<phi> vp1
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | (Formula.Until \<phi> I \<psi>, VUntilInf i hi vp2s) \<Rightarrow>
    (hi = (case right I of enat b \<Rightarrow> LTP_f \<sigma> i b) \<and> right I \<noteq> \<infinity>
    \<and> map v_at vp2s = [ETP_f \<sigma> i I ..< hi + 1]
    \<and> (\<forall>vp2 \<in> set vp2s. v_check_exec vs \<psi> vp2))
  | ( _ , _) \<Rightarrow> False)"

declare s_check_exec.simps[simp del] v_check_exec.simps[simp del]
simps_of_case s_check_exec_simps[simp, code]: s_check_exec.simps[unfolded prod.case] (splits: Formula.formula.split sproof.split)
simps_of_case v_check_exec_simps[simp, code]: v_check_exec.simps[unfolded prod.case] (splits: Formula.formula.split vproof.split)

definition AD :: "'d Formula.formula \<Rightarrow> nat \<Rightarrow> 'd set"
  where "AD \<phi> i = Formula.consts \<phi> \<union> (\<Union> k \<le> the (LRTP \<sigma> \<phi> i). \<Union> (set ` snd ` \<Gamma> \<sigma> k))"

lemma val_in_AD_iff:
  "x \<in> Formula.fv \<phi> \<Longrightarrow> v x \<in> AD \<phi> i \<longleftrightarrow> v x \<in> Formula.consts \<phi> \<or>
  (\<exists>r ts k. k \<le> the (LRTP \<sigma> \<phi> i) \<and> (r, Formula.eval_trms v ts) \<in> \<Gamma> \<sigma> k \<and> x \<in> \<Union> (set (map Formula.fv_trm ts)))"
  apply (intro iffI)
  unfolding AD_def Un_iff
   apply (erule disj_mono[rule_format, rotated -1])
    apply assumption
   apply clarsimp
   apply (rename_tac k' r' ds')
   apply (rule_tac x=r' in exI)
   apply (rule_tac x="map (\<lambda>d. if v x = d then (Formula.Var x::'d Formula.trm) else Formula.Const d) ds'" in exI)
   apply (rule_tac x=k' in exI)
  unfolding Formula.eval_trms_def apply clarsimp
  subgoal for k' p' ds'
    apply (subgoal_tac "map (Formula.eval_trm v \<circ> (\<lambda>d. if v x = d then Formula.Var x else Formula.Const d)) ds' = ds'")
     apply clarsimp
    apply (simp add: map_idI)
    done
   apply (erule disj_mono[rule_format, rotated -1])
    apply assumption
   apply clarsimp
  subgoal for p' ts' k' t'
    apply (cases t'; clarsimp)
    apply (rule_tac x=k' in bexI)
    apply (rule bexI[of _ "(p', Formula.eval_trms v ts')"])
    apply (simp_all add: Formula.eval_trms_def)
    using image_iff apply fastforce
    done
  done

lemma val_notin_AD_iff:
  "x \<in> Formula.fv \<phi> \<Longrightarrow> v x \<notin> AD \<phi> i \<longleftrightarrow> v x \<notin> Formula.consts \<phi> \<and>
    (\<forall>r ts k. k \<le> the (LRTP \<sigma> \<phi> i) \<and> x \<in> \<Union> (set (map Formula.fv_trm ts)) \<longrightarrow> (r, Formula.eval_trms v ts) \<notin> \<Gamma> \<sigma> k)"
  using val_in_AD_iff by blast

lemma fv_formula_fv_trm:
  assumes "x \<in> Formula.fv (formula.Pred r ts)"
  shows "\<exists>t \<in> set ts. x \<in> Formula.fv_trm t"
  using assms by auto

lemma eval_trm_val_eq: "Formula.eval_trm v x = Formula.eval_trm v' x \<Longrightarrow> (case x of Formula.Var x \<Rightarrow> v x = v' x | Formula.Const x \<Rightarrow> True)"
  by (simp split: trm.splits) auto

unbundle MFOTL_notation \<comment> \<open> enable notation \<close>

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

lemma finite_values: "finite (\<Union> (set ` snd ` \<Gamma> \<sigma> k))"
  by (transfer, auto simp add: sfstfinite_def)

lemma finite_tps: "Formula.future_bounded \<phi> \<Longrightarrow> finite (\<Union> k < the (LRTP \<sigma> \<phi> i). {k})"
  using fb_LRTP[of \<phi>] finite_enat_bounded 
  by simp

lemma finite_AD [simp]: "Formula.future_bounded \<phi> \<Longrightarrow> finite (AD \<phi> i)"
  using finite_tps finite_values
  by (simp add: AD_def enat_def)

lemma finite_AD_UNIV: 
  assumes "Formula.future_bounded \<phi>" and "AD \<phi> i = (UNIV:: 'd set)"
  shows "finite (UNIV::'d set)"
proof -
  have "finite (AD \<phi> i)"
    using finite_AD[of \<phi> i, OF assms(1)] by simp
  then show ?thesis
    using assms(2) by simp
qed

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
  case (Eq_Const x c)
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

lemma compatible_vals_nonemptyI: "\<forall>x. vs x \<noteq> {} \<Longrightarrow> compatible_vals A vs \<noteq> {}"
  by (auto simp: compatible_vals_def intro!: bchoice)

lemma check_exec_check:
  assumes "\<forall>x. vs x \<noteq> {}"
  shows "s_check_exec vs \<phi> sp \<longleftrightarrow> (\<forall>v \<in> compatible_vals (fv \<phi>) vs. s_check v \<phi> sp)" 
    and "v_check_exec vs \<phi> vp \<longleftrightarrow> (\<forall>v \<in> compatible_vals (fv \<phi>) vs. v_check v \<phi> vp)"
  using assms
proof (induct \<phi> arbitrary: vs sp vp)
  case TT
  {
    case 1
    then show ?case using compatible_vals_nonemptyI
      by (cases sp)
        auto
  next
    case 2
    then show ?case using compatible_vals_nonemptyI
      by auto
  }
next
  case FF
  {
    case 1
    then show ?case using compatible_vals_nonemptyI
      by (cases sp)
        auto
  next
    case 2
    then show ?case using compatible_vals_nonemptyI 
      by (cases vp)
        auto
  }
next
  case (Pred p ts)
  {
    case 1
    have obs: "\<forall>tX\<in>set (Formula.eval_trms_set vs ts). snd tX \<noteq> {}"
      using \<open>\<forall>x. vs x \<noteq> {}\<close>
      by (induct ts; clarsimp simp: Formula.eval_trms_set_def)
        (rule_tac y=a in Formula.trm.exhaust; clarsimp)
    show ?case
      using 1 compatible_vals_nonemptyI[OF 1]
      apply (cases sp; clarsimp simp: mk_values_subset_iff[OF obs] subset_eq  simp del: fv.simps)
      apply (intro iffI conjI impI allI ballI)
           apply clarsimp
          apply clarsimp
         apply (elim conjE, clarsimp simp del: fv.simps)
      using mk_values_complete apply force
      using mk_values_sound by blast+
  next
    case 2
    then show ?case using compatible_vals_nonemptyI[OF 2]
      apply (cases vp; clarsimp simp: subset_eq mk_values_subset_Compl_def simp del: fv.simps)
      apply (intro iffI conjI impI allI ballI)
           apply clarsimp
           apply clarsimp
         apply (elim conjE, clarsimp simp del: fv.simps)
      apply (metis Formula.eval_trms_set_def mk_values_complete)
      using mk_values_sound apply blast
        using mk_values_sound apply blast
        by (metis Formula.eval_trms_set_def mk_values_sound)
  }
next
  case (Eq_Const x c)
  {
    case 1
    then show ?case
      by (cases sp) (auto simp: compatible_vals_def)
  next
    case 2
    then show ?case
      by (cases vp) (auto simp: compatible_vals_def)
  }
next
  case (Neg \<phi>)
  {
    case 1
    then show ?case
      using Neg.hyps(2) compatible_vals_nonemptyI[OF 1]
      by (cases sp) auto
  next
    case 2
    then show ?case 
      using Neg.hyps(1) compatible_vals_nonemptyI[OF 2]
      by (cases vp) auto
  }
next
  case (Or \<phi>1 \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SOrL sp')
      from check_fv_cong(1)[of \<phi>1 _ _ sp'] show ?thesis
        unfolding SOrL s_check_exec_simps s_check_simps fv.simps Or(1)[OF 1, of sp']
        by (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
    next
      case (SOrR sp')
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SOrR s_check_exec_simps s_check_simps fv.simps Or(3)[OF 1, of sp']
        by (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VOr vp1 vp2)
      from check_fv_cong(2)[of \<phi>1 _ _ vp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding VOr v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
           Or(2)[OF 2, of vp1]  Or(4)[OF 2, of vp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
        done
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (And \<phi>1 \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SAnd sp1 sp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(1)[of \<phi>2 _ _ sp2] show ?thesis
        unfolding SAnd s_check_exec_simps s_check_simps fv.simps ball_conj_distrib
           And(1)[OF 1, of sp1] And(3)[OF 1, of sp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        using compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
        done
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VAndL vp')
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding VAndL v_check_exec_simps v_check_simps fv.simps And(2)[OF 2, of vp']
        by (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
    next
      case (VAndR vp')
      from check_fv_cong(2)[of \<phi>2 _ _ vp'] show ?thesis
        unfolding VAndR v_check_exec_simps v_check_simps fv.simps And(4)[OF 2, of vp']
        by (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (Imp \<phi>1 \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SImpL vp')
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding SImpL s_check_exec_simps s_check_simps fv.simps Imp(2)[OF 1, of vp']
        by (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
    next
      case (SImpR sp')
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SImpR s_check_exec_simps s_check_simps fv.simps Imp(3)[OF 1, of sp']
        by (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VImp sp1 vp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding VImp v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
           Imp(1)[OF 2, of sp1] Imp(4)[OF 2, of vp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
        done
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (Iff \<phi>1 \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SIffSS sp1 sp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(1)[of \<phi>2 _ _ sp2] show ?thesis
        unfolding SIffSS s_check_exec_simps s_check_simps fv.simps ball_conj_distrib
           Iff(1)[OF 1, of sp1] Iff(3)[OF 1, of sp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        using compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
        done
    next
      case (SIffVV vp1 vp2)
      from check_fv_cong(2)[of \<phi>1 _ _ vp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding SIffVV s_check_exec_simps s_check_simps fv.simps ball_conj_distrib
           Iff(2)[OF 1, of vp1] Iff(4)[OF 1, of vp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        using compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
        done
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VIffSV sp1 vp2)
      from check_fv_cong(1)[of \<phi>1 _ _ sp1] check_fv_cong(2)[of \<phi>2 _ _ vp2] show ?thesis
        unfolding VIffSV v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
           Iff(1)[OF 2, of sp1] Iff(4)[OF 2, of vp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
        done
    next
      case (VIffVS vp1 sp2)
      from check_fv_cong(2)[of \<phi>1 _ _ vp1] check_fv_cong(1)[of \<phi>2 _ _ sp2] show ?thesis
        unfolding VIffVS v_check_exec_simps v_check_simps fv.simps ball_conj_distrib
           Iff(2)[OF 2, of vp1] Iff(3)[OF 2, of sp2]
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"])
        apply (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        apply (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
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
    from 1 show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi> - {x}"]
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
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi> - {x}"]
      by (cases vp)
        (auto simp: SubsVals_nonempty IH[OF SubsVals_nonempty]
        fun_upd_in_compatible_vals fun_upd_in_compatible_vals_notin compatible_vals_fun_upd
        ball_conj_distrib 2[simplified] split: prod.splits if_splits |
        drule bspec, assumption)+
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
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi> - {x}"]
      by (cases sp)
        (auto simp: SubsVals_nonempty IH[OF SubsVals_nonempty]
        fun_upd_in_compatible_vals fun_upd_in_compatible_vals_notin compatible_vals_fun_upd
        ball_conj_distrib 1[simplified] split: prod.splits if_splits |
        drule bspec, assumption)+
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
    from 2 show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi> - {x}"]
      by (cases vp) (auto simp: SubsVals_nonempty IH fun_upd_in_compatible_vals_notin compatible_vals_fun_upd)
  }
next
  case (Prev I \<phi>)
  {
    case 1
    with Prev[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) auto
  next
    case 2
    with Prev[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) auto
  }
next
  case (Next I \<phi>)
  {
    case 1
    with Next[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) (auto simp: Let_def)
  next
    case 2
    with Next[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) auto
  }
next
  case (Once I \<phi>)
  {
    case 1
    with Once[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) (auto simp: Let_def)
  next
    case 2
    with Once[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) auto
  }
next
  case (Historically I \<phi>)
  {
    case 1
    with Historically[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) auto
  next
    case 2
    with Historically[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) (auto simp: Let_def)
  }
next
  case (Eventually I \<phi>)
  {
    case 1
    with Eventually[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) (auto simp: Let_def)
  next
    case 2
    with Eventually[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) auto
  }
next
  case (Always I \<phi>)
  {
    case 1
    with Always[of vs] show ?case
      using compatible_vals_nonemptyI[OF 1, of "fv \<phi>"]
      by (cases sp) auto
  next
    case 2
    with Always[of vs] show ?case
      using compatible_vals_nonemptyI[OF 2, of "fv \<phi>"]
      by (cases vp) (auto simp: Let_def)
  }
next
  case (Since \<phi>1 I \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SSince sp' sps)
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SSince s_check_exec_simps s_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set sps"]
          Since(1)[OF 1] Since(3)[OF 1, of sp'] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set sps", OF refl])
             using compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
            using compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
           using compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
          using compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
         apply (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        subgoal for sp
          using check_fv_cong(1)[of \<phi>1 _ _ sp]
          apply (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
          done
        done
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VSince i vp' vps)
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding VSince v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Since(2)[OF 2, of vp'] Since(4)[OF 2] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl])
             using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
            using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
           using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
          using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
         apply (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        subgoal for vp
          using check_fv_cong(2)[of \<phi>2 _ _ vp]
          apply (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
          done
        done
    next
      case (VSinceInf i j vps)
      show ?thesis
        unfolding VSinceInf v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Since(4)[OF 2] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl])
           using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
          using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
         using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
        subgoal for vp
          using check_fv_cong(2)[of \<phi>2 _ _ vp]
          apply (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
          done
        done
    qed (auto simp: compatible_vals_union_eq)
  }
next
  case (Until \<phi>1 I \<phi>2)
  {
    case 1
    with compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases sp)
      case (SUntil sps sp')
      from check_fv_cong(1)[of \<phi>2 _ _ sp'] show ?thesis
        unfolding SUntil s_check_exec_simps s_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set sps"]
          Until(1)[OF 1] Until(3)[OF 1, of sp'] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set sps", OF refl])
             using compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
            using compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
           using compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
          using compatible_vals_nonemptyI[OF 1, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
         apply (metis (mono_tags, lifting) 1 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
        subgoal for sp
          using check_fv_cong(1)[of \<phi>1 _ _ sp]
          apply (metis (mono_tags, lifting) 1 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
          done
        done
    qed (auto simp: compatible_vals_union_eq)
  next
    case 2
    with compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] show ?case
    proof (cases vp)
      case (VUntil i vps vp')
      from check_fv_cong(2)[of \<phi>1 _ _ vp'] show ?thesis
        unfolding VUntil v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Until(2)[OF 2, of vp'] Until(4)[OF 2] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl])
             using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
            using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
           using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
         apply (metis (mono_tags, lifting) 2 IntE Un_upper1 compatible_vals_extensible compatible_vals_union_eq)
        subgoal for vp
          using check_fv_cong(2)[of \<phi>2 _ _ vp]
          apply (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
          done
        done
    next
      case (VUntilInf i j vps)
      show ?thesis
        unfolding VUntilInf v_check_exec_simps v_check_simps fv.simps ball_conj_distrib ball_swap[of _ "set vps"]
          Until(4)[OF 2] Let_def
        apply (intro arg_cong2[of _ _ _ _ "(\<and>)"] ball_cong[of "set vps", OF refl])
           using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
          using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
         using compatible_vals_nonemptyI[OF 2, of "fv \<phi>1 \<union> fv \<phi>2"] apply blast
        subgoal for vp
          using check_fv_cong(2)[of \<phi>2 _ _ vp]
          apply (metis (mono_tags, lifting) 2 IntE Un_upper2 compatible_vals_extensible compatible_vals_union_eq)
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

unbundle MFOTL_no_notation \<comment> \<open> disable notation \<close>

lemma AD_simps[simp]:
  "AD (Formula.Neg \<phi>) i = AD \<phi> i"
  "Formula.future_bounded (Formula.Or \<phi> \<psi>) \<Longrightarrow> AD (Formula.Or \<phi> \<psi>) i = AD \<phi> i \<union> AD \<psi> i"
  "Formula.future_bounded (Formula.And \<phi> \<psi>) \<Longrightarrow> AD (Formula.And \<phi> \<psi>) i = AD \<phi> i \<union> AD \<psi> i"
  "Formula.future_bounded (Formula.Imp \<phi> \<psi>) \<Longrightarrow> AD (Formula.Imp \<phi> \<psi>) i = AD \<phi> i \<union> AD \<psi> i"
  "Formula.future_bounded (Formula.Iff \<phi> \<psi>) \<Longrightarrow> AD (Formula.Iff \<phi> \<psi>) i = AD \<phi> i \<union> AD \<psi> i"
  "AD (Formula.Exists x \<phi>) i = AD \<phi> i"
  "AD (Formula.Forall x \<phi>) i = AD \<phi> i"
  "AD (Formula.Prev I \<phi>) i = AD \<phi> (i - 1)"
  "AD (Formula.Next I \<phi>) i = AD \<phi> (i + 1)"
  "Formula.future_bounded (Formula.Eventually I \<phi>) \<Longrightarrow> AD (Formula.Eventually I \<phi>) i = AD \<phi> (LTP_f \<sigma> i (the_enat (right I)))"
  "Formula.future_bounded (Formula.Always I \<phi>) \<Longrightarrow> AD (Formula.Always I \<phi>) i = AD \<phi> (LTP_f \<sigma> i (the_enat (right I)))"
  "AD (Formula.Once I \<phi>) i = AD \<phi> (LTP_p_safe \<sigma> i I)"
  "AD (Formula.Historically I \<phi>) i = AD \<phi> (LTP_p_safe \<sigma> i I)"
  "Formula.future_bounded (Formula.Since \<phi> I \<psi>) \<Longrightarrow> AD (Formula.Since \<phi> I \<psi>) i = AD \<phi> i \<union> AD \<psi> (LTP_p_safe \<sigma> i I)"
  "Formula.future_bounded (Formula.Until \<phi> I \<psi>) \<Longrightarrow> AD (Formula.Until \<phi> I \<psi>) i = AD \<phi> (LTP_f \<sigma> i (the_enat (right I)) - 1) \<union> AD \<psi> (LTP_f \<sigma> i (the_enat (right I)))"
  by (auto 0 3 simp: AD_def max_opt_def not_none_fb_LRTP le_max_iff_disj Bex_def split: option.splits)


lemma LTP_p_mono: "i \<le> j \<Longrightarrow> LTP_p_safe \<sigma> i I \<le> LTP_p_safe \<sigma> j I"
  unfolding LTP_p_safe_def
  apply (auto simp: i_LTP_tau min_def le_diff_conv split: if_splits)
      apply (metis \<tau>_mono diff_diff_cancel diff_is_0_eq' nat_le_linear)
     apply (metis \<tau>_mono diff_diff_cancel diff_is_0_eq' nat_le_linear)
    apply (metis \<tau>_mono diff_diff_cancel diff_is_0_eq' nat_le_linear)
   apply (meson \<tau>_mono diff_le_mono order.trans i_LTP_tau order_refl)
  apply (meson \<tau>_mono diff_le_mono order.trans i_LTP_tau order_refl)
  done

lemma LTP_f_mono: "i \<le> j \<Longrightarrow> LTP_f \<sigma> i b \<le> LTP_f \<sigma> j b"
  apply (auto simp: LTP_def finite_nat_set_iff_bounded_le intro!: Max_mono elim: order_trans dest!: spec[of _ i])
  by (metis i_le_LTPi_add le_iff_add)

lemma LRTP_mono: "Formula.future_bounded \<phi> \<Longrightarrow> i \<le> j \<Longrightarrow> the (LRTP \<sigma> \<phi> i) \<le> the (LRTP \<sigma> \<phi> j)"
  apply (induct \<phi> arbitrary: i j)
                   apply (auto simp: max_opt_def not_none_fb_LRTP le_max_iff_disj LTP_f_mono diff_le_mono dest: LTP_p_mono LTP_f_mono split: option.splits)
             apply force
            apply force
           apply force
          apply force
         apply force
        apply force
       apply force
      apply force
     apply force
    apply (metis LTP_p_mono option.sel)
   apply (metis Checker.LTP_f_mono diff_le_mono option.sel)
  apply (metis Checker.LTP_f_mono option.sel)
  done

lemma AD_mono: "Formula.future_bounded \<phi> \<Longrightarrow> i \<le> j \<Longrightarrow> AD \<phi> i \<subseteq> AD \<phi> j"
  by (auto 0 3 simp: AD_def Bex_def intro: LRTP_mono elim!: order_trans)

lemma LTP_p_safe_le[simp]: "LTP_p_safe \<sigma> i I \<le> i"
  by (auto simp: LTP_p_safe_def)

lemma check_AD_cong:
  assumes "Formula.future_bounded \<phi>"
    and "(\<forall>x \<in> Formula.fv \<phi>. v x = v' x \<or> (v x \<notin> AD \<phi> i \<and> v' x \<notin> AD \<phi> i))"
  shows "(s_at sp = i \<Longrightarrow> s_check v \<phi> sp \<longleftrightarrow> s_check v' \<phi> sp)"
        "(v_at vp = i \<Longrightarrow> v_check v \<phi> vp \<longleftrightarrow> v_check v' \<phi> vp)"
  using assms
proof (induction v \<phi> sp and v \<phi> vp arbitrary: i v' and i v' rule: s_check_v_check.induct)
  case (1 v f sp)
  note IH = 1(1-23)[OF refl] and hyps = 1(24-26)
  show ?case
  proof (cases sp)
    case (SPred j r ts)
    then show ?thesis
    proof (cases f)
      case (Pred q us)
      with SPred hyps show ?thesis
        apply (auto simp: val_notin_AD_iff)
         apply (subst Formula.eval_trms_fv_cong; force)
        apply (subst Formula.eval_trms_fv_cong; force)
        done
    qed auto
  next
    case (SEq_Const j r ts)
    with hyps show ?thesis
      by (cases f) (auto simp: val_notin_AD_iff)
  next
    case (SNeg vp')
    then show ?thesis
      using IH(1)[of _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SOrL sp')
    then show ?thesis
      using IH(2)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SOrR sp')
    then show ?thesis
      using IH(3)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SAnd sp1 sp2)
    then show ?thesis
      using IH(4,5)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (SImpL vp')
    then show ?thesis
      using IH(6)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SImpR sp')
    then show ?thesis
      using IH(7)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SIffSS sp1 sp2)
    then show ?thesis
      using IH(8,9)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (SIffVV vp1 vp2)
    then show ?thesis
      using IH(10,11)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (SExists x z sp')
    then show ?thesis
      using IH(12)[of x _ x z sp' i "v'(x := z)"] hyps
      by (cases f) (auto simp add: fun_upd_def)
  next
    case (SForall x part)
    then show ?thesis
      using IH(13)[of x _ x part _ _ D _ z _ "v'(x := z)" for D z, OF _ _ _ _  refl _ refl] hyps
      by (cases f) (auto simp add: fun_upd_def)
  next
    case (SPrev sp')
    then show ?thesis
      using IH(14)[of _ _ _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (SNext sp')
    then show ?thesis
      using IH(15)[of _ _ _ _ _ _ v'] hyps
      by (cases f) (auto simp add: Let_def)
  next
    case (SOnce j sp')
    then show ?thesis
    proof (cases f)
      case (Once I \<phi>)
      { fix k
        assume k: "k \<le> i" "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> k"
        then have "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> 0"
          by (meson \<tau>_mono le0 order_trans)
        with k have "k \<le> LTP_p_safe \<sigma> i I"
          unfolding LTP_p_safe_def by (auto simp: i_LTP_tau)
        with Once hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Once SOnce show ?thesis
        using IH(16)[OF Once SOnce refl refl, of v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2)
    qed auto
  next
    case (SHistorically j k sps)
    then show ?thesis
    proof (cases f)
      case (Historically I \<phi>)
      { fix sp :: "'d sproof"
        define l and u where "l = s_at sp" and "u = LTP_p \<sigma> i I"
        assume *: "sp \<in> set sps" "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
        then have u_def: "u = LTP_p_safe \<sigma> i I"
          by (auto simp: LTP_p_safe_def u_def)
        from *(1) obtain j where j: "sp = sps ! j" "j < length sps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map s_at sps = [k ..< Suc u]"
        then have len: "length sps = Suc u - k"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "s_at (sps ! j) = k + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len *(2)
          by (auto simp: nth_append)
        ultimately have "l \<le> u"
          unfolding l_def by auto
        with Historically hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto simp: u_def dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Historically SHistorically show ?thesis
        using IH(17)[OF Historically SHistorically _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  next
    case (SEventually j sp')
    then show ?thesis
    proof (cases f)
      case (Eventually I \<phi>)
      { fix k
        assume "\<tau> \<sigma> k \<le> the_enat (right I) + \<tau> \<sigma> i"
        then have "k \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (metis add.commute i_le_LTPi_add le_add_diff_inverse)
        with Eventually hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Eventually SEventually show ?thesis
        using IH(18)[OF Eventually SEventually refl refl, of v'] hyps(1,2)
        by (auto simp: Let_def)
    qed auto
  next
    case (SAlways j k sps)
    then show ?thesis
    proof (cases f)
      case (Always I \<phi>)
      { fix sp :: "'d sproof"
        define l and u where "l = s_at sp" and "u = LTP_f \<sigma> i (the_enat (right I))"
        assume *: "sp \<in> set sps"
        then obtain j where j: "sp = sps ! j" "j < length sps"
          unfolding in_set_conv_nth by auto
        assume eq: "map s_at sps = [ETP_f \<sigma> i I ..< Suc u]"
        then have "length sps = Suc u - ETP_f \<sigma> i I"
          by (auto dest!: arg_cong[where f=length])
        with j eq have "l \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (auto simp: l_def u_def dest!: arg_cong[where f="\<lambda>xs. nth xs j"]
            simp del: upt.simps split: if_splits)
        with Always hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Always SAlways show ?thesis
        using IH(19)[OF Always SAlways _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  next
    case (SSince sp' sps)
    then show ?thesis
    proof (cases f)
      case (Since \<phi> I \<psi>)
      { fix sp :: "'d sproof"
        define l where "l = s_at sp"
        assume *: "sp \<in> set sps"
        from *(1) obtain j where j: "sp = sps ! j" "j < length sps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map s_at sps = [Suc (s_at sp')  ..< Suc i]"
        then have len: "length sps = i - s_at sp'"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "s_at (sps ! j) = Suc (s_at sp') + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len
          by (auto simp: nth_append)
        ultimately have "l \<le> i"
          unfolding l_def by auto
        with Since hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto simp: dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      moreover
      { fix k
        assume k: "k \<le> i" "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> k"
        then have "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> 0"
          by (meson \<tau>_mono le0 order_trans)
        with k have "k \<le> LTP_p_safe \<sigma> i I"
          unfolding LTP_p_safe_def by (auto simp: i_LTP_tau)
        with Since hyps(2,3) have "\<forall>x\<in>Formula.fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> k \<and> v' x \<notin> AD \<psi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      ultimately show ?thesis
        using Since SSince IH(20)[OF Since SSince refl refl refl, of v'] IH(21)[OF Since SSince refl refl _ refl, of _ v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2 simp del: upt.simps)
    qed auto
  next
    case (SUntil sps sp')
    then show ?thesis
    proof (cases f)
      case (Until \<phi> I \<psi>)
      { fix sp :: "'d sproof"
        define l where "l = s_at sp"
        assume *: "sp \<in> set sps"
        from *(1) obtain j where j: "sp = sps ! j" "j < length sps"
          unfolding in_set_conv_nth by auto
        moreover
        assume "\<delta> \<sigma> (s_at sp') i \<le> the_enat (right I)"
        then have "s_at sp' \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (metis add.commute i_le_LTPi_add le_add_diff_inverse le_diff_conv)
        moreover
        assume eq: "map s_at sps = [i ..< s_at sp']"
        then have len: "length sps = s_at sp' - i"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "s_at (sps ! j) = i + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len
          by (auto simp: nth_append)
        ultimately have "l \<le> LTP_f \<sigma> i (the_enat (right I)) - 1"
          unfolding l_def by auto
        with Until hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto simp: dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      moreover
      { fix k
        assume "\<tau> \<sigma> k \<le> the_enat (right I) + \<tau> \<sigma> i"
        then have "k \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (metis add.commute i_le_LTPi_add le_add_diff_inverse)
        with Until hyps(2,3) have "\<forall>x\<in>Formula.fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> k \<and> v' x \<notin> AD \<psi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      ultimately show ?thesis
        using Until SUntil IH(22)[OF Until SUntil refl refl refl, of v'] IH(23)[OF Until SUntil refl refl _ refl, of _ v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2 simp del: upt.simps)
    qed auto
  qed (cases f; simp_all)+
next
  case (2 v f vp)
  note IH = 2(1-25)[OF refl] and hyps = 2(26-28)
  show ?case
  proof (cases vp)
    case (VPred j r ts)
    then show ?thesis
    proof (cases f)
      case (Pred q us)
      with VPred hyps show ?thesis
        apply (auto simp: val_notin_AD_iff)
         apply (subst (asm) (3) Formula.eval_trms_fv_cong; force)
        apply (subst (asm) (3) Formula.eval_trms_fv_cong; force)
        done
    qed auto
  next
    case (VEq_Const j r ts)
    with hyps show ?thesis
      by (cases f) (auto simp: val_notin_AD_iff)
  next
    case (VNeg sp')
    then show ?thesis
      using IH(1)[of _ _ _ v'] hyps
      by (cases f) auto
  next
    case (VOr vp1 vp2)
    then show ?thesis
      using IH(2,3)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (VAndL vp')
    then show ?thesis
      using IH(4)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (VAndR vp')
    then show ?thesis
      using IH(5)[of _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (VImp sp1 vp2)
    then show ?thesis
      using IH(6,7)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (VIffSV sp1 vp2)
    then show ?thesis
      using IH(8,9)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (VIffVS vp1 sp2)
    then show ?thesis
      using IH(10,11)[of _ _ _ _ _ v'] hyps
      by (cases f) (auto 7 0)+
  next
    case (VExists x part)
    then show ?thesis
      using IH(12)[of x _ x part _ _ D _ z _ "v'(x := z)" for D z, OF _ _ _ _  refl _ refl] hyps
      by (cases f) (auto simp add: fun_upd_def)
  next
    case (VForall x z vp')
    then show ?thesis
      using IH(13)[of x _ x z vp' i "v'(x := z)"] hyps
      by (cases f) (auto simp add: fun_upd_def)
  next
    case (VPrev vp')
    then show ?thesis
      using IH(14)[of _ _ _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (VNext vp')
    then show ?thesis
      using IH(15)[of _ _ _ _ _ _ v'] hyps
      by (cases f) auto
  next
    case (VOnce j k vps)
    then show ?thesis
    proof (cases f)
      case (Once I \<phi>)
      { fix vp :: "'d vproof"
        define l and u where "l = v_at vp" and "u = LTP_p \<sigma> i I"
        assume *: "vp \<in> set vps" "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
        then have u_def: "u = LTP_p_safe \<sigma> i I"
          by (auto simp: LTP_p_safe_def u_def)
        from *(1) obtain j where j: "vp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map v_at vps = [k ..< Suc u]"
        then have len: "length vps = Suc u - k"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "v_at (vps ! j) = k + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len *(2)
          by (auto simp: nth_append)
        ultimately have "l \<le> u"
          unfolding l_def by auto
        with Once hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto simp: u_def dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Once VOnce show ?thesis
        using IH(16)[OF Once VOnce _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  next
    case (VHistorically j vp')
    then show ?thesis
    proof (cases f)
      case (Historically I \<phi>)
      { fix k
        assume k: "k \<le> i" "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> k"
        then have "\<tau> \<sigma> i - left I \<ge> \<tau> \<sigma> 0"
          by (meson \<tau>_mono le0 order_trans)
        with k have "k \<le> LTP_p_safe \<sigma> i I"
          unfolding LTP_p_safe_def by (auto simp: i_LTP_tau)
        with Historically hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Historically VHistorically show ?thesis
        using IH(17)[OF Historically VHistorically refl refl, of v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2)
    qed auto
  next
    case (VEventually j k vps)
    then show ?thesis
    proof (cases f)
      case (Eventually I \<phi>)
      { fix vp :: "'d vproof"
        define l and u where "l = v_at vp" and "u = LTP_f \<sigma> i (the_enat (right I))"
        assume *: "vp \<in> set vps"
        then obtain j where j: "vp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        assume eq: "map v_at vps = [ETP_f \<sigma> i I ..< Suc u]"
        then have "length vps = Suc u - ETP_f \<sigma> i I"
          by (auto dest!: arg_cong[where f=length])
        with j eq have "l \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (auto simp: l_def u_def dest!: arg_cong[where f="\<lambda>xs. nth xs j"]
            simp del: upt.simps split: if_splits)
        with Eventually hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> l \<and> v' x \<notin> AD \<phi> l"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Eventually VEventually show ?thesis
        using IH(18)[OF Eventually VEventually _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  next
    case (VAlways j vp')
    then show ?thesis
    proof (cases f)
      case (Always I \<phi>)
      { fix k
        assume "\<tau> \<sigma> k \<le> the_enat (right I) + \<tau> \<sigma> i"
        then have "k \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (metis add.commute i_le_LTPi_add le_add_diff_inverse)
        with Always hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Always VAlways show ?thesis
        using IH(19)[OF Always VAlways refl refl, of v'] hyps(1,2)
        by (auto simp: Let_def)
    qed auto
  next
    case (VSince j vp' vps)
    then show ?thesis
    proof (cases f)
      case (Since \<phi> I \<psi>)
      { fix sp :: "'d vproof"
        define l and u where "l = v_at sp" and "u = LTP_p \<sigma> i I"
        assume *: "sp \<in> set vps" "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
        then have u_def: "u = LTP_p_safe \<sigma> i I"
          by (auto simp: LTP_p_safe_def u_def)
        from *(1) obtain j where j: "sp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map v_at vps = [v_at vp'  ..< Suc u]"
        then have len: "length vps = Suc u - v_at vp'"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "v_at (vps ! j) = v_at vp' + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len
          by (auto simp: nth_append)
        ultimately have "l \<le> u"
          unfolding l_def by auto
        with Since hyps(2,3) have "\<forall>x\<in>Formula.fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> l \<and> v' x \<notin> AD \<psi> l"
          by (auto simp: u_def dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      moreover
      { fix k
        assume k: "k \<le> i"
        with Since hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      ultimately show ?thesis
        using Since VSince IH(20)[OF Since VSince refl refl, of v'] IH(21)[OF Since VSince refl _ refl, of _ v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2 simp del: upt.simps)
    qed auto
  next
    case (VSinceInf j k vps)
    then show ?thesis
    proof (cases f)
      case (Since \<phi> I \<psi>)
      { fix vp :: "'d vproof"
        define l and u where "l = v_at vp" and "u = LTP_p \<sigma> i I"
        assume *: "vp \<in> set vps" "\<tau> \<sigma> 0 + left I \<le> \<tau> \<sigma> i"
        then have u_def: "u = LTP_p_safe \<sigma> i I"
          by (auto simp: LTP_p_safe_def u_def)
        from *(1) obtain j where j: "vp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map v_at vps = [k ..< Suc u]"
        then have len: "length vps = Suc u - k"
          by (auto dest!: arg_cong[where f=length])
        moreover
        have "v_at (vps ! j) = k + j"
          using arg_cong[where f="\<lambda>xs. nth xs j", OF eq] j len *(2)
          by (auto simp: nth_append)
        ultimately have "l \<le> u"
          unfolding l_def by auto
        with Since hyps(2,3) have "\<forall>x\<in>Formula.fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> l \<and> v' x \<notin> AD \<psi> l"
          by (auto simp: u_def dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Since VSinceInf show ?thesis
        using IH(22)[OF Since VSinceInf _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  next
    case (VUntil j vps vp')
    then show ?thesis
    proof (cases f)
      case (Until \<phi> I \<psi>)
      { fix sp :: "'d vproof"
        define l and u where "l = v_at sp" and "u = v_at vp'"
        assume *: "sp \<in> set vps" "v_at vp' \<le> LTP_f \<sigma> i (the_enat (right I))"
        from *(1) obtain j where j: "sp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        moreover
        assume eq: "map v_at vps = [ETP_f \<sigma> i I ..< Suc u]"
        then have "length vps = Suc u - ETP_f \<sigma> i I"
          by (auto dest!: arg_cong[where f=length])
        with j eq *(2) have "l \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (auto simp: l_def u_def dest!: arg_cong[where f="\<lambda>xs. nth xs j"]
            simp del: upt.simps split: if_splits)
        with Until hyps(2,3) have "\<forall>x\<in>Formula.fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> l \<and> v' x \<notin> AD \<psi> l"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      moreover
      { fix k
        assume "k < LTP_f \<sigma> i (the_enat (right I))"
        then have "k \<le> LTP_f \<sigma> i (the_enat (right I)) - 1"
          by linarith
        with Until hyps(2,3) have "\<forall>x\<in>Formula.fv \<phi>. v x = v' x \<or> v x \<notin> AD \<phi> k \<and> v' x \<notin> AD \<phi> k"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      ultimately show ?thesis
        using Until VUntil IH(23)[OF Until VUntil refl refl, of v'] IH(24)[OF Until VUntil refl _ refl, of _ v'] hyps(1,2)
        by (auto simp: Let_def le_diff_conv2 simp del: upt.simps)
    qed auto
  next
    case (VUntilInf j k vps)
    then show ?thesis
    proof (cases f)
      case (Until \<phi> I \<psi>)
      { fix vp :: "'d vproof"
        define l and u where "l = v_at vp" and "u = LTP_f \<sigma> i (the_enat (right I))"
        assume *: "vp \<in> set vps"
        then obtain j where j: "vp = vps ! j" "j < length vps"
          unfolding in_set_conv_nth by auto
        assume eq: "map v_at vps = [ETP_f \<sigma> i I ..< Suc u]"
        then have "length vps = Suc u - ETP_f \<sigma> i I"
          by (auto dest!: arg_cong[where f=length])
        with j eq have "l \<le> LTP_f \<sigma> i (the_enat (right I))"
          by (auto simp: l_def u_def dest!: arg_cong[where f="\<lambda>xs. nth xs j"]
            simp del: upt.simps split: if_splits)
        with Until hyps(2,3) have "\<forall>x\<in>Formula.fv \<psi>. v x = v' x \<or> v x \<notin> AD \<psi> l \<and> v' x \<notin> AD \<psi> l"
          by (auto dest!: bspec dest: AD_mono[THEN set_mp, rotated -1])
      }
      with Until VUntilInf show ?thesis
        using IH(25)[OF Until VUntilInf _ refl, of _ v'] hyps(1,2)
        by auto
    qed auto
  qed (cases f; simp_all)+
qed

lemma part_hd_tabulate: "distinct xs \<Longrightarrow> part_hd (tabulate xs f z) = (case xs of [] \<Rightarrow> z | (x # _) \<Rightarrow> (if set xs = UNIV then f x else z))"
  by (transfer, auto split: list.splits)

lemma s_at_tabulate:
  assumes "\<forall>z. s_at (mypick z) = i" 
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> AD \<phi> i))" 
  shows "\<forall>(sub, vp) \<in> SubsVals mypart. s_at vp = i"
  using assms by (transfer, auto)

lemma v_at_tabulate:
  assumes "\<forall>z. v_at (mypick z) = i" 
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> AD \<phi> i))" 
  shows "\<forall>(sub, vp) \<in> SubsVals mypart. v_at vp = i"
  using assms by (transfer, auto)

lemma s_check_tabulate:
  assumes "Formula.future_bounded \<phi>"
    and "\<forall>z. s_at (mypick z) = i" 
    and "\<forall>z. s_check (v(x:=z)) \<phi> (mypick z)"
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> AD \<phi> i))"
  shows "\<forall>(sub, vp) \<in> SubsVals mypart. \<forall>z \<in> sub. s_check (v(x := z)) \<phi> vp"
  using assms 
  apply (transfer fixing: \<sigma>)
  apply clarsimp
  subgoal for \<phi> mypick i v x z
  proof -
    assume s_at_assm: "\<forall>z. s_at (mypick z) = i" 
      and s_check_assm: "\<forall>z. s_check (v(x := z)) \<phi> (mypick z)"
      and fb_assm: "Formula.future_bounded \<phi>"
      and z_notin_AD: "z \<notin> (AD \<phi> i)"
    have s_at_mypick: "s_at (mypick (SOME z. z \<notin> local.AD \<phi> i)) = i"
      using s_at_assm by simp
    have s_check_mypick: "Checker.s_check \<sigma> (v(x := SOME z. z \<notin> AD \<phi> i)) \<phi> (mypick (SOME z. z \<notin> AD \<phi> i))"
      using s_check_assm by simp
    show ?thesis
      using z_notin_AD
      apply (subst check_AD_cong(1)[of \<phi> "v(x := z)" "v(x := (SOME z. z \<notin> Checker.AD \<sigma> \<phi> i))" i "mypick (SOME z. z \<notin> AD \<phi> i)", OF fb_assm _ s_at_mypick])
       apply (auto simp add: someI[of "\<lambda>z. z \<notin> AD \<phi> i" z] s_check_mypick fb_assm split: if_splits)
      done
  qed
  done

lemma v_check_tabulate:
  assumes "Formula.future_bounded \<phi>"
    and "\<forall>z. v_at (mypick z) = i" 
    and "\<forall>z. v_check (v(x:=z)) \<phi> (mypick z)"
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> AD \<phi> i))"
  shows "\<forall>(sub, vp) \<in> SubsVals mypart. \<forall>z \<in> sub. v_check (v(x := z)) \<phi> vp"
  using assms 
  apply (transfer fixing: \<sigma>)
  apply clarsimp
  subgoal for \<phi> mypick i v x z
  proof -
    assume v_at_assm: "\<forall>z. v_at (mypick z) = i" 
      and v_check_assm: "\<forall>z. v_check (v(x := z)) \<phi> (mypick z)"
      and fb_assm: "Formula.future_bounded \<phi>"
      and z_notin_AD: "z \<notin> (AD \<phi> i)"
    have v_at_mypick: "v_at (mypick (SOME z. z \<notin> local.AD \<phi> i)) = i"
      using v_at_assm by simp
    have v_check_mypick: "Checker.v_check \<sigma> (v(x := SOME z. z \<notin> AD \<phi> i)) \<phi> (mypick (SOME z. z \<notin> AD \<phi> i))"
      using v_check_assm by simp
    show ?thesis
      using z_notin_AD
      apply (subst check_AD_cong(2)[of \<phi> "v(x := z)" "v(x := (SOME z. z \<notin> Checker.AD \<sigma> \<phi> i))" i "mypick (SOME z. z \<notin> AD \<phi> i)", OF fb_assm _ v_at_mypick])
       apply (auto simp add: someI[of "\<lambda>z. z \<notin> AD \<phi> i" z] v_check_mypick fb_assm split: if_splits)
      done
  qed
  done

lemma s_at_part_hd_tabulate: 
  assumes "Formula.future_bounded \<phi>"
    and "\<forall>z. s_at (f z) = i"
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) f (f (SOME z. z \<notin> AD \<phi> i))"
  shows "s_at (part_hd mypart) = i"
  using assms by (simp add: part_hd_tabulate split: list.splits)

lemma v_at_part_hd_tabulate: 
  assumes "Formula.future_bounded \<phi>"
    and "\<forall>z. v_at (f z) = i"
    and "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) f (f (SOME z. z \<notin> AD \<phi> i))"
  shows "v_at (part_hd mypart) = i"
  using assms by (simp add: part_hd_tabulate split: list.splits)

lemma check_completeness:
  "(SAT \<sigma> v i \<phi> \<longrightarrow> Formula.future_bounded \<phi> \<longrightarrow> (\<exists>sp. s_at sp = i \<and> s_check v \<phi> sp)) \<and>
   (VIO \<sigma> v i \<phi> \<longrightarrow> Formula.future_bounded \<phi> \<longrightarrow> (\<exists>vp. v_at vp = i \<and> v_check v \<phi> vp))"
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
  case (SEq_Const v x c i)
  then show ?case
    apply simp
    apply (rule exI[of _ "SEq_Const i x c"])
    apply simp
    done
next
  case (VEq_Const v x c i)
  then show ?case
    apply simp
    apply (rule exI[of _ "VEq_Const i x c"])
    apply simp
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
  show ?case
  proof
    assume "Formula.future_bounded (Formula.Exists x \<phi>)"
    then have fb: "Formula.future_bounded \<phi>"
      by simp
    obtain mypick where mypick_def: "v_at (mypick z) = i \<and> v_check (v(x:=z)) \<phi> (mypick z)" for z
      using VExists fb
      apply (atomize_elim)
      apply (rule choice)
      apply simp
      done 
    define mypart where "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> (AD \<phi> i)))"
    have mypick_at: "\<forall>z. v_at (mypick z) = i"
      by (simp add: mypick_def)
    have mypick_v_check: "\<forall>z. v_check (v(x:=z)) \<phi> (mypick z)" 
      by (simp add: mypick_def)
    have mypick_v_check2: "\<forall>z. v_check (v(x := (SOME z. z \<notin> AD \<phi> i))) \<phi> (mypick (SOME z. z \<notin> AD \<phi> i))"
      by (simp add: mypick_def)
    have v_at_myp: "v_at (VExists x mypart) = i"
      using v_at_part_hd_tabulate[OF fb, of mypick i]
      by (simp add: mypart_def mypick_def) 
    have v_check_myp: "v_check v (Formula.Exists x \<phi>) (VExists x mypart)"
      apply (simp add: mypart_def v_at_part_hd_tabulate[OF fb mypick_at])
      apply clarify
      apply (rule conjI)
      using v_at_tabulate[of mypick i _ \<phi>, OF mypick_at] apply fastforce
      using v_check_tabulate[OF fb mypick_at mypick_v_check] apply fastforce
      done            
    show "\<exists>vp. v_at vp = i \<and> v_check v (Formula.Exists x \<phi>) vp"
      using v_at_myp v_check_myp by blast
  qed
next
  case (SForall v x i \<phi>)
  show ?case 
  proof
    assume "Formula.future_bounded (Formula.Forall x \<phi>)"
    then have fb: "Formula.future_bounded \<phi>"
      by simp
    obtain mypick where mypick_def: "s_at (mypick z) = i \<and> s_check (v(x:=z)) \<phi> (mypick z)" for z
      using SForall fb 
      apply (atomize_elim)
      apply (rule choice)
      apply simp
      done 
    define mypart where "mypart = tabulate (sorted_list_of_set (AD \<phi> i)) mypick (mypick (SOME z. z \<notin> (AD \<phi> i)))"
    have mypick_at: "\<forall>z. s_at (mypick z) = i"
      by (simp add: mypick_def)
    have mypick_s_check: "\<forall>z. s_check (v(x:=z)) \<phi> (mypick z)" 
      by (simp add: mypick_def)
    have mypick_s_check2: "\<forall>z. s_check (v(x := (SOME z. z \<notin> AD \<phi> i))) \<phi> (mypick (SOME z. z \<notin> AD \<phi> i))"
      by (simp add: mypick_def)
    have s_at_myp: "s_at (SForall x mypart) = i"
      using s_at_part_hd_tabulate[OF fb, of mypick i]
      by (simp add: mypart_def mypick_def) 
    have s_check_myp: "s_check v (Formula.Forall x \<phi>) (SForall x mypart)"
      apply (simp add: mypart_def s_at_part_hd_tabulate[OF fb mypick_at])
      apply clarify
      apply (rule conjI)
      using s_at_tabulate[of mypick i _ \<phi>, OF mypick_at] apply fastforce
      using s_check_tabulate[OF fb mypick_at mypick_s_check] apply fastforce
      done
    show "\<exists>sp. s_at sp = i \<and> s_check v (Formula.Forall x \<phi>) sp"
      using s_at_myp s_check_myp by blast
  qed
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
  show ?case 
  proof
    assume "Formula.future_bounded (Formula.Once I \<phi>)"
    then have fb: "Formula.future_bounded \<phi>"
      by simp
    obtain mypick where mypick_def: "\<forall>k \<in> {j .. LTP_p \<sigma> i I}. v_at (mypick k) = k \<and> v_check v \<phi> (mypick k)"
      using VOnce fb
      apply (atomize_elim)
      apply (rule bchoice)
      apply simp
      done
    then obtain vps where vps_def: "map (v_at) vps = [j ..< Suc (LTP_p \<sigma> i I)] \<and> (\<forall>vp \<in> set vps. v_check v \<phi> vp)"
      apply atomize_elim 
      apply (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([j ..< Suc (LTP_p \<sigma> i I)])"])
      done
    then have "v_at (VOnce i j vps) = i \<and> v_check v (Formula.Once I \<phi>) (VOnce i j vps)"
      using VOnce by auto
    then show "\<exists>vp. v_at vp = i \<and> v_check v (Formula.Once I \<phi>) vp"
      by blast
  qed
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
  show ?case 
  proof
    assume fb_eventually: "Formula.future_bounded (Formula.Eventually I \<phi>)"
    then have fb: "Formula.future_bounded \<phi>"
      by simp
    obtain b where b_def: "right I = enat b"
      using fb_eventually by (atomize_elim, cases "right I") auto
    define j where j_def: "j = LTP \<sigma> (\<tau> \<sigma> i + b)"
    obtain mypick where mypick_def: "\<forall>k \<in> {ETP_f \<sigma> i I .. j}. v_at (mypick k) = k \<and> v_check v \<phi> (mypick k)"
      using VEventually fb_eventually
      apply (atomize_elim)
      apply (rule bchoice)
      apply (simp add: b_def j_def)
      done
    then obtain vps where vps_def: "map (v_at) vps = [ETP_f \<sigma> i I ..< Suc j] \<and> (\<forall>vp \<in> set vps. v_check v \<phi> vp)"
      apply atomize_elim 
      apply (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([ETP_f \<sigma> i I ..< Suc j])"])
      done
    then have "v_at (VEventually i j vps) = i \<and> v_check v (Formula.Eventually I \<phi>) (VEventually i j vps)"
      using VEventually b_def j_def by simp
    then show "\<exists>vp. v_at vp = i \<and> v_check v (Formula.Eventually I \<phi>) vp"
      by blast
  qed
next
  case (SHistorically j I i v \<phi>)
  show ?case
  proof
    assume fb_historically: "Formula.future_bounded (Formula.Historically I \<phi>)"
    then have fb: "Formula.future_bounded \<phi>"
      by simp
    obtain mypick where mypick_def: "\<forall>k \<in> {j .. LTP_p \<sigma> i I}. s_at (mypick k) = k \<and> s_check v \<phi> (mypick k)"
      using SHistorically fb
      apply (atomize_elim)
      apply (rule bchoice)
      apply simp
      done
    then obtain sps where sps_def: "map (s_at) sps = [j ..< Suc (LTP_p \<sigma> i I)] \<and> (\<forall>sp \<in> set sps. s_check v \<phi> sp)"
      apply atomize_elim 
      apply (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([j ..< Suc (LTP_p \<sigma> i I)])"])
      done
    then have "s_at (SHistorically i j sps) = i \<and> s_check v (Formula.Historically I \<phi>) (SHistorically i j sps)"
      using SHistorically by auto
    then show "\<exists>sp. s_at sp = i \<and> s_check v (Formula.Historically I \<phi>) sp"
      by blast
  qed
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
  show ?case 
  proof
    assume fb_always: "Formula.future_bounded (Formula.Always I \<phi>)"
    then have fb: "Formula.future_bounded \<phi>"
      by simp
    obtain b where b_def: "right I = enat b"
      using fb_always by (atomize_elim, cases "right I") auto
    define j where j_def: "j = LTP \<sigma> (\<tau> \<sigma> i + b)"
    obtain mypick where mypick_def: "\<forall>k \<in> {ETP_f \<sigma> i I .. j}. s_at (mypick k) = k \<and> s_check v \<phi> (mypick k)"
      using SAlways fb_always
      apply (atomize_elim)
      apply (rule bchoice)
      apply (simp add: b_def j_def)
      done
    then obtain sps where sps_def: "map (s_at) sps = [ETP_f \<sigma> i I ..< Suc j] \<and> (\<forall>sp \<in> set sps. s_check v \<phi> sp)"
      apply atomize_elim 
      apply (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([ETP_f \<sigma> i I ..< Suc j])"])
      done
    then have "s_at (SAlways i j sps) = i \<and> s_check v (Formula.Always I \<phi>) (SAlways i j sps)"
      using SAlways b_def j_def by simp
    then show "\<exists>sp. s_at sp = i \<and> s_check v (Formula.Always I \<phi>) sp"
      by blast
  qed
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
  show ?case 
  proof
    assume fb_since: "Formula.future_bounded (Formula.Since \<phi> I \<psi>)"
    then have fb: "Formula.future_bounded \<phi>" "Formula.future_bounded \<psi>"
      by simp_all
    obtain sp2 where sp2_def: "s_at sp2 = j \<and> s_check v \<psi> sp2" 
      using SSince fb_since 
      apply atomize_elim
      apply auto
      done
    { 
      assume "Suc j > i"
      then have "s_at (SSince sp2 []) = i \<and> s_check v (Formula.Since \<phi> I \<psi>) (SSince sp2 [])"
        using sp2_def SSince by auto
      then have "\<exists>sp. s_at sp = i \<and> s_check v (Formula.Since \<phi> I \<psi>) sp" 
        by blast
    }
    moreover
    {
      assume sucj_leq_i: "Suc j \<le> i"
      obtain mypick where mypick_def: "\<forall>k \<in> {Suc j ..< Suc i}. s_at (mypick k) = k \<and> s_check v \<phi> (mypick k)"
        using SSince fb_since
        apply (atomize_elim)
        apply (rule bchoice)
        apply simp
        done
      then obtain sp1s where sp1s_def: "map (s_at) sp1s = [Suc j ..< Suc i] \<and> (\<forall>sp \<in> set sp1s. s_check v \<phi> sp)"
        apply atomize_elim 
        apply (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([Suc j ..< Suc i])"])
        done
      then have "sp1s \<noteq> []" 
        using sucj_leq_i by auto
      then have "s_at (SSince sp2 sp1s) = i \<and> s_check v (Formula.Since \<phi> I \<psi>) (SSince sp2 sp1s)"
        using SSince sucj_leq_i fb
        unfolding sp2_def sp1s_def
        apply (clarsimp simp add: Let_def split: list.splits)
        apply (smt (verit, best) Cons_eq_upt_conv last.simps last_map last_snoc list.set_intros(1) list.set_intros(2) list.simps(9) sp1s_def sp2_def upt_Suc)
        done
      then have "\<exists>sp. s_at sp = i \<and> s_check v (Formula.Since \<phi> I \<psi>) sp"
        by blast
    }
    ultimately show "\<exists>sp. s_at sp = i \<and> s_check v (Formula.Since \<phi> I \<psi>) sp"
      using not_less by blast
  qed
next
  case (VSinceOut i I v \<phi> \<psi>)
  then show ?case 
    apply clarsimp
    apply (rule exI[of _ "VSinceOut i"])
    apply (simp add: fun_upd_def)
    done
next
  case (VSince I i j v \<phi> \<psi>)
  show ?case 
  proof
    assume fb_since: "Formula.future_bounded (Formula.Since \<phi> I \<psi>)"
    then have fb: "Formula.future_bounded \<phi>" "Formula.future_bounded \<psi>"
      by simp_all
    obtain vp1 where vp1_def: "v_at vp1 = j \<and> v_check v \<phi> vp1" 
      using fb_since VSince by auto
    obtain mypick where mypick_def: "\<forall>k \<in> {j .. LTP_p \<sigma> i I}. v_at (mypick k) = k \<and> v_check v \<psi> (mypick k)"
      using VSince fb_since
      apply (atomize_elim)
      apply (rule bchoice)
      apply simp
      done
    then obtain vp2s where vp2s_def: "map (v_at) vp2s = [j ..< Suc (LTP_p \<sigma> i I)] \<and> (\<forall>vp \<in> set vp2s. v_check v \<psi> vp)"
      apply atomize_elim 
      apply (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([j ..< Suc (LTP_p \<sigma> i I)])"])
      done
    then have "v_at (VSince i vp1 vp2s) = i \<and> v_check v (Formula.Since \<phi> I \<psi>) (VSince i vp1 vp2s)"
      using vp1_def VSince by auto
    then show "\<exists>vp. v_at vp = i \<and> v_check v (Formula.Since \<phi> I \<psi>) vp"
      by blast
  qed
next
  case (VSinceInf j I i v \<psi> \<phi>)
  show ?case 
  proof
    assume fb_since: "Formula.future_bounded (Formula.Since \<phi> I \<psi>)"
    then have fb: "Formula.future_bounded \<phi>" "Formula.future_bounded \<psi>"
      by simp_all
    obtain mypick where mypick_def: "\<forall>k \<in> {j .. LTP_p \<sigma> i I}. v_at (mypick k) = k \<and> v_check v \<psi> (mypick k)"
      using VSinceInf fb_since
      apply (atomize_elim)
      apply (rule bchoice)
      apply simp
      done
    then obtain vp2s where vp2s_def: "map (v_at) vp2s = [j ..< Suc (LTP_p \<sigma> i I)] \<and> (\<forall>vp \<in> set vp2s. v_check v \<psi> vp)"
      apply atomize_elim 
      apply (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([j ..< Suc (LTP_p \<sigma> i I)])"])
      done
    then have "v_at (VSinceInf i j vp2s) = i \<and> v_check v (Formula.Since \<phi> I \<psi>) (VSinceInf i j vp2s)"
      using VSinceInf by auto
    then show "\<exists>vp. v_at vp = i \<and> v_check v (Formula.Since \<phi> I \<psi>) vp"
      by blast
  qed
next
  case (SUntil j i I v \<psi> \<phi>)
  show ?case
  proof
    assume fb_until: "Formula.future_bounded (Formula.Until \<phi> I \<psi>)"
    then have fb: "Formula.future_bounded \<phi>" "Formula.future_bounded \<psi>"
      by simp_all
    obtain sp2 where sp2_def: "s_at sp2 = j \<and> s_check v \<psi> sp2" 
      using fb SUntil by blast
    {
      assume "i \<ge> j"
      then have "s_at (SUntil [] sp2) = i \<and> s_check v (Formula.Until \<phi> I \<psi>) (SUntil [] sp2)"
        using sp2_def SUntil by auto
      then have "\<exists>sp. s_at sp = i \<and> s_check v (Formula.Until \<phi> I \<psi>) sp" 
        by blast
    }
    moreover
    {
      assume i_l_j: "i < j"
      obtain mypick where mypick_def: "\<forall>k \<in> {i ..< j}. s_at (mypick k) = k \<and> s_check v \<phi> (mypick k)"
        using SUntil fb_until
        apply (atomize_elim)
        apply (rule bchoice)
        apply simp
        done
      then obtain sp1s where sp1s_def: "map (s_at) sp1s = [i ..< j] \<and> (\<forall>sp \<in> set sp1s. s_check v \<phi> sp)"
        apply atomize_elim 
        apply (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([i ..< j])"])
        done
      then have "s_at (SUntil sp1s sp2) = i \<and> s_check v (Formula.Until \<phi> I \<psi>) (SUntil sp1s sp2)"
        using SUntil fb_until
        unfolding sp2_def sp1s_def
        apply (clarsimp simp add: Let_def split: list.splits)
        apply (metis (no_types, lifting) Cons_eq_upt_conv i_l_j less_nat_zero_code list.map_disc_iff list.simps(9) sp2_def upt_eq_Nil_conv)
        done
      then have "\<exists>sp. s_at sp = i \<and> s_check v (Formula.Until \<phi> I \<psi>) sp"
        by blast
    }
    ultimately show "\<exists>sp. s_at sp = i \<and> s_check v (Formula.Until \<phi> I \<psi>) sp"
      using not_less by blast
  qed
next
  case (VUntil I j i v \<phi> \<psi>)
  show ?case
  proof
    assume fb_until: "Formula.future_bounded (Formula.Until \<phi> I \<psi>)"
    then have fb: "Formula.future_bounded \<phi>" "Formula.future_bounded \<psi>"
      by simp_all
    obtain vp1 where vp1_def: "v_at vp1 = j \<and> v_check v \<phi> vp1" 
      using VUntil fb_until by auto
    obtain mypick where mypick_def: "\<forall>k \<in> {ETP_f \<sigma> i I .. j}. v_at (mypick k) = k \<and> v_check v \<psi> (mypick k)"
      using VUntil fb_until
      apply (atomize_elim)
      apply (rule bchoice)
      apply simp
      done
    then obtain vp2s where vp2s_def: "map (v_at) vp2s = [ETP_f \<sigma> i I ..< Suc j] \<and> (\<forall>vp \<in> set vp2s. v_check v \<psi> vp)"
      apply atomize_elim 
      apply (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([ETP_f \<sigma> i I ..< Suc j])"])
      done
    then have "v_at (VUntil i vp2s vp1) = i \<and> v_check v (Formula.Until \<phi> I \<psi>) (VUntil i vp2s vp1)"
      using VUntil fb_until vp1_def by simp
    then show "\<exists>vp. v_at vp = i \<and> v_check v (Formula.Until \<phi> I \<psi>) vp"
      by blast
  qed
next
  case (VUntilInf I i v \<psi> \<phi>)
  show ?case
  proof
    assume fb_until: "Formula.future_bounded (Formula.Until \<phi> I \<psi>)"
    then have fb: "Formula.future_bounded \<phi>" "Formula.future_bounded \<psi>"
      by simp_all
    obtain b where b_def: "right I = enat b"
      using fb_until by (atomize_elim, cases "right I") auto
    define j where j_def: "j = LTP \<sigma> (\<tau> \<sigma> i + b)"
    obtain mypick where mypick_def: "\<forall>k \<in> {ETP_f \<sigma> i I .. j}. v_at (mypick k) = k \<and> v_check v \<psi> (mypick k)"
      using VUntilInf fb_until
      apply (atomize_elim)
      apply (rule bchoice)
      apply (simp add: b_def j_def)
      done
    then obtain vp2s where vp2s_def: "map (v_at) vp2s = [ETP_f \<sigma> i I ..< Suc j] \<and> (\<forall>vp \<in> set vp2s. v_check v \<psi> vp)"
      apply atomize_elim 
      apply (auto intro!: trans[OF list.map_cong list.map_id] exI[of _ "map mypick ([ETP_f \<sigma> i I ..< Suc j])"])
      done
    then have "v_at (VUntilInf i j vp2s) = i \<and> v_check v (Formula.Until \<phi> I \<psi>) (VUntilInf i j vp2s)"
      using VUntilInf b_def j_def by simp
    then show "\<exists>vp. v_at vp = i \<and> v_check v (Formula.Until \<phi> I \<psi>) vp"
      by blast
  qed
qed

definition "p_at = (\<lambda>p. case_sum s_at v_at p)"

definition "p_check_exec = (\<lambda>vs \<phi> p. case_sum (s_check_exec vs \<phi>) (v_check_exec vs \<phi>) p)"

definition valid :: "'d Formula.envset \<Rightarrow> nat \<Rightarrow> 'd Formula.formula \<Rightarrow> 'd proof \<Rightarrow> bool" where
  "valid vs i \<phi> p = 
    (case p of
      Inl p \<Rightarrow> s_check_exec vs \<phi> p \<and> s_at p = i
    | Inr p \<Rightarrow> v_check_exec vs \<phi> p \<and> v_at p = i)"

inductive sat_vorder :: "Formula.name list \<Rightarrow> 'd expl \<Rightarrow> bool" where
  "sat_vorder vars (Leaf _)"
| "\<forall>expl \<in> Vals part1. sat_vorder vars expl \<Longrightarrow> sat_vorder (x # vars) (Node x part1)"
| "sat_vorder vars (Node x part1) \<Longrightarrow> x \<noteq> z \<Longrightarrow> sat_vorder (z # vars) (Node x part1)"

end

end