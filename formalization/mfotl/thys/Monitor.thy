(*<*)
theory Monitor
  imports Proof_System
begin
(*>*)

fun apply_pdt :: "'d expl \<Rightarrow> 'd expl \<Rightarrow> 'd MFOTL.trm list \<Rightarrow> 'd expl" where
  "apply_pdt explL explR vars = (if ((vars_expl explL) \<inter> (vars_expl explR) = \<emptyset>) then 
                                   (case explL of Leaf \<Rightarrow> (case explR of Leaf pt \<Rightarrow> explL
                                                           | Node x part \<Rightarrow> explL )
                                    | Node x part \<Rightarrow> (case explR of Leaf pt \<Rightarrow> explL
                                                           | Node x part \<Rightarrow> explL ))
                                 else explR)"

end