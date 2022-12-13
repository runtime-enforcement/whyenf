(*<*)
theory Monitor
  imports Proof_System
begin
(*>*)

context fixes \<sigma> :: "'a MFOTL.trace"
begin

consts s_at :: "'d sproof \<Rightarrow> nat"
consts v_at :: "'d vproof \<Rightarrow> nat"

find_theorems "_ \<subseteq> - _"
find_consts "_ set list"

primrec eval_trm where
  "eval_trm v (MFOTL.Var x) = v x"
| "eval_trm v (MFOTL.Const x) = {x}"

fun s_check and v_check where
  "s_check v f p = (case (f, p) of
    (MFOTL.TT, STT i) \<Rightarrow> True
  | (MFOTL.Pred r ts, SPred i pred ts') \<Rightarrow> (r = pred \<and> ts = ts' \<and> 
    {r} \<times> listset (map (eval_trm v) ts) \<subseteq> \<Gamma> \<sigma> i)
  | (MFOTL.Forall x \<phi>, SForall part) \<Rightarrow> True
  | (_, _) \<Rightarrow> False)"
| "v_check v f p = (case (f, p) of
    (MFOTL.FF, VFF i) \<Rightarrow> True
  | (MFOTL.Pred r ts, VPred i pred ts') \<Rightarrow> (r = pred \<and> ts = ts' \<and> 
    {r} \<times> listset (map (eval_trm v) ts) \<subseteq> - \<Gamma> \<sigma> i)
  | (_, _) \<Rightarrow> False)" 
end

end