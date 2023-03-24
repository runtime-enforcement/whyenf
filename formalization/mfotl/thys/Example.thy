(*<*)
theory Example
  imports Proof_System
begin
(*>*)

setup_lifting type_definition_part

lift_definition trivial_part :: "'v \<Rightarrow> ('d, 'v) part" is "\<lambda>v. [(UNIV, v)]"
  by auto

lift_definition point_part :: "'d \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('d, 'v) part" is "\<lambda>d v1 v2. [({d}, v1), (UNIV - {d}, v2)]"
  by (auto simp add: less_Suc_eq)

term "let leaf = (Leaf (Inr (VAndL (VPred 2 ''publish'' [MFOTL.Var a, MFOTL.Var f])))) in
      let evproof = \<lambda>i. VExists (trivial_part (VPred i ''approve'' [MFOTL.Var m, MFOTL.Var f])) in
  Node a (point_part ''Alice'' 
    (Node f (point_part ''160'' (Leaf (Inl (SAnd (SPred 2 ''publish'' [MFOTL.Var a, MFOTL.Var f]) 
            (SNeg (VOnce 2 0 (map evproof [0,1,2])))))) leaf))
  leaf) :: string expl"

end