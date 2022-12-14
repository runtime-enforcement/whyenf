(*<*)
theory Monitor
  imports Proof_System
begin
(*>*)

lift_definition part_hd :: "('d, 'a) part \<Rightarrow> 'a" is "snd \<circ> hd" .

lemma part_hd_estimation[termination_simp]: "size (part_hd xs) < size_part f g xs"
  sorry

lemma size_last_estimation[termination_simp]: "xs \<noteq> [] \<Longrightarrow> size (last xs) < size_list size xs"
  by (induct xs) auto

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
| "s_at (SForall part) = s_at (part_hd part)" (* s_at (part_hd part) *)
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
| "v_at (VExists part) = undefined"
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
  apply clarify
  apply (measures "[f1,f2,f3]")

context fixes \<sigma> :: "'a MFOTL.trace"

begin

primrec eval_trm :: "(string \<Rightarrow> 'a set) \<Rightarrow> 'a MFOTL.trm \<Rightarrow> 'a set" where
  "eval_trm v (MFOTL.Var x) = v x"
| "eval_trm v (MFOTL.Const x) = {x}"

value "listset[{1::nat, 2}, {2::nat,3}]"
find_theorems listset

fun s_check and v_check where
  "s_check v vs f p = (case (f, p) of
    (MFOTL.TT, STT i) \<Rightarrow> True
  | (MFOTL.Pred r ts, SPred i s ts') \<Rightarrow> (r = s \<and> ts = ts' \<and> 
    {r} \<times> listset (map (eval_trm v) ts) \<subseteq> \<Gamma> \<sigma> i)
  | (MFOTL.Forall x \<phi>, SForall part) \<Rightarrow> True
  | (_, _) \<Rightarrow> False)"
| "v_check v vs f p = (case (f, p) of
    (MFOTL.FF, VFF i) \<Rightarrow> True
  | (MFOTL.Pred r ts, VPred i pred ts') \<Rightarrow> (r = pred \<and> ts = ts' \<and> 
    {r} \<times> listset (map (eval_trm v) ts) \<subseteq> - \<Gamma> \<sigma> i)
  | (_, _) \<Rightarrow> False)" 

end

end