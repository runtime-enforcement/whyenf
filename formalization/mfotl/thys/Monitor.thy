(*<*)
theory Monitor
  imports Proof_System
begin
(*>*)

setup_lifting type_definition_partition

lift_definition trivial_partition :: "'v \<Rightarrow> ('d, 'v) partition" is "\<lambda>v. [(UNIV, v)]"
  by auto

lift_definition point_partition :: "'d \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('d, 'v) partition" is "\<lambda>d v1 v2. [({d}, v1), (UNIV - {d}, v2)]"
  by (auto simp add: less_Suc_eq)

term " let leaf0 = (Leaf (Inr (VAndL (VPred 2 ''publish'' [MFOTL.Var a, MFOTL.Var f]))));
       evproof = \<lambda>i. VExists (trivial_partition (VPred i ''approve'' [MFOTL.Var m, MFOTL.Var f])) in
  Node a (point_partition ''Alice'' 
  (Node f (point_partition ''160'' (Leaf (Inl (SAnd (SPred 2 ''publish'' [MFOTL.Var a, MFOTL.Var f]) 
                                   (SNeg (VOnce 2 0 (map evproof [0,1,2])))))) leaf0))
  leaf0) :: (string, string) expl"

end