theory Examples
  imports Checker_Code Whymon.Monitor
begin


unbundle MFOTL_notation \<comment> \<open> enable notation \<close>

(* value "v\<lbrakk>\<^bold>c (0::nat)\<rbrakk> = 0"

term "\<forall>\<^sub>F''x''. \<exists>\<^sub>F''y''. (P \<dagger> [\<^bold>c a, \<^bold>v ''x'']) \<and>\<^sub>F Q \<dagger> [\<^bold>v ''y''] \<longrightarrow>\<^sub>F \<phi> \<^bold>U I \<psi>"

value "\<^bold>Y I (\<not>\<^sub>F (P \<dagger> [\<^bold>c a, \<^bold>v ''x'']) \<and>\<^sub>F (Q \<dagger> [\<^bold>v y])) \<^bold>S (point n) ((\<^bold>X \<^bold>[2,3\<^bold>] (P \<dagger> [\<^bold>c b, \<^bold>v ''x''])) \<or>\<^sub>F Q \<dagger> [\<^bold>v ''y''])
 = Formula.Since (Formula.Prev I (Formula.And (Formula.Neg (Formula.Pred P [\<^bold>c a, \<^bold>v ''x''])) (Formula.Pred Q [\<^bold>v y]))) 
  (point n) (Formula.Or (Formula.Next \<^bold>[2,3\<^bold>] (Formula.Pred P [\<^bold>c b, \<^bold>v ''x''])) (Formula.Pred Q [\<^bold>v ''y'']))"

term "\<langle>\<sigma>, v, i\<rangle> \<Turnstile> \<^bold>Y I (\<not>\<^sub>F (P \<dagger> [\<^bold>c a, \<^bold>v ''x'']) \<and>\<^sub>F (Q \<dagger> [\<^bold>v y])) \<^bold>S (point n) ((\<^bold>X \<^bold>[2,3\<^bold>] (P \<dagger> [\<^bold>c b, \<^bold>v ''x''])) \<or>\<^sub>F Q \<dagger> [\<^bold>v ''y''])" *)

unbundle MFOTL_no_notation \<comment> \<open> disable notation \<close>

(* instance string8 :: infinite sorry

definition string8_string where 
  "string8_string s = string8_literal (String.implode s)"

definition execute_trivial_eval where
 "execute_trivial_eval \<sigma> vars i \<phi> = eval \<sigma> (\<lambda>p1 p2. (p_pred (\<lambda> _. 1) p1) \<le> (p_pred (\<lambda> _. 1) p2)) vars i \<phi>"

(* Example 1 *)
definition mytrace :: "event_data Formula.trace" where 
  "mytrace = trace_of_list [({}, 1::nat),
                            ({(string8_string ''publish'', [EInt 2])}, 2::nat),
                            ({(string8_string ''publish'', [EInt 2]),
                              (string8_string ''approve'', [EInt 3])}, 3::nat),
                            ({(string8_string ''publish'', [EInt 3]),
                              (string8_string ''approve'', [EInt 3])}, 4::nat)]"

definition phi1 :: "event_data Formula.formula" where
  "phi1 = Formula.And (Formula.Pred (string8_string ''publish'') [Formula.Var (string8_string ''r'')]) 
                    (Formula.Pred (string8_string ''approve'') [Formula.Var (string8_string ''r'')])"

definition phi2 :: "event_data Formula.formula" where
  "phi2 = Formula.Exists (string8_string ''last'') (Formula.Pred (string8_string ''p'') 
                                                   [Formula.Var (string8_string ''first'')])"

value "execute_trivial_eval mytrace [string8_string ''r''] (3::nat) phi1"

definition "check_trivial_eval \<sigma> vs i \<phi> = (let e = execute_trivial_eval \<sigma> vs i \<phi> in check_all \<sigma> \<phi> e)"

value "check_trivial_eval mytrace [string8_string ''r''] (3::nat) phi1"

definition mytrace4 :: "event_data Formula.trace" where 
  "mytrace4 = trace_of_list
     [({(string8_string ''mgr_S'', [EString (string8_string ''Mallory''), EString (string8_string ''Alice'')]),
        (string8_string ''mgr_S'', [EString (string8_string ''Merlin''), EString (string8_string ''Bob'')]),
        (string8_string ''mgr_S'', [EString (string8_string ''Merlin''), EString (string8_string ''Charlie'')])}, 1307532861::nat),
      ({(string8_string ''approve'', [EString (string8_string ''Mallory''), EString (string8_string ''152'')])}, 1307532861),
      ({(string8_string ''approve'', [EString (string8_string ''Merlin''), EString (string8_string ''163'')]),
        (string8_string ''publish'', [EString (string8_string ''Alice''), EString (string8_string ''160'')]),
        (string8_string ''mgr_F'', [EString (string8_string ''Merlin''), EString (string8_string ''Charlie'')])}, 1307955600),
      ({(string8_string ''approve'', [EString (string8_string ''Merlin''), EString (string8_string ''187'')]),
        (string8_string ''publish'', [EString (string8_string ''Bob''), EString (string8_string ''163'')]),
        (string8_string ''publish'', [EString (string8_string ''Alice''), EString (string8_string ''163'')]),
        (string8_string ''publish'', [EString (string8_string ''Charlie''), EString (string8_string ''163'')]),
        (string8_string ''publish'', [EString (string8_string ''Charlie''), EString (string8_string ''152'')])}, 1308477599)]"

definition phi4 :: "event_data Formula.formula" where
  "phi4 = Formula.Imp (Formula.Pred (string8_string ''publish'') [Formula.Var (string8_string ''a''), Formula.Var (string8_string ''r'')])
    (Formula.Once (init 604800) (Formula.Exists (string8_string ''m'') (Formula.Since 
      (Formula.Neg (Formula.Pred (string8_string ''mgr_F'') [Formula.Var (string8_string ''m''), Formula.Var (string8_string ''a'')])) all
      (Formula.And (Formula.Pred (string8_string ''mgr_S'') [Formula.Var (string8_string ''m''), Formula.Var (string8_string ''a'')])
                 (Formula.Pred (string8_string ''approve'') [Formula.Var (string8_string ''m''), Formula.Var (string8_string ''r'')])))))"

value "execute_trivial_eval mytrace4 [string8_string ''a'', string8_string ''r''] 3 phi4"
value "check_trivial_eval mytrace4 [string8_string ''a'', string8_string ''r''] 3 phi4"

(*exemption for report id 163*)
definition phi4' :: "event_data Formula.formula" where
  "phi4' = Formula.Imp (Formula.Pred (string8_string ''publish'') [Formula.Var (string8_string ''a''), Formula.Var (string8_string ''r'')])
    (Formula.Or (Formula.Eq_Const (string8_string ''r'') (EString (string8_string ''163''))) (Formula.Once (init 604800) (Formula.Exists (string8_string ''m'') (Formula.Since 
      (Formula.Neg (Formula.Pred (string8_string ''mgr_F'') [Formula.Var (string8_string ''m''), Formula.Var (string8_string ''a'')])) all
      (Formula.And (Formula.Pred (string8_string ''mgr_S'') [Formula.Var (string8_string ''m''), Formula.Var (string8_string ''a'')])
                 (Formula.Pred (string8_string ''approve'') [Formula.Var (string8_string ''m''), Formula.Var (string8_string ''r'')]))))))"


value "execute_trivial_eval mytrace4 [string8_string ''a'', string8_string ''r''] 3 phi4'"
value "check_trivial_eval mytrace4 [string8_string ''a'', string8_string ''r''] 3 phi4'"

definition phi5 :: "event_data Formula.formula" where
  "phi5 = Formula.Pred (string8_string ''publish'') [Formula.Var (string8_string ''a''), Formula.Var (string8_string ''r'')]"

definition mytrace6 :: "event_data Formula.trace" where 
  "mytrace6 = trace_of_list [({}, 1::nat),
                            ({(string8_string ''p'', [EInt 3])}, 2::nat),
                            ({}, 3::nat),
                            ({}, 4::nat)]"

definition phi7 :: "event_data Formula.formula" where
  "phi7 = Formula.Forall (string8_string ''x'') 
          (Formula.Imp
            (Formula.Neg (Formula.Pred (string8_string ''c'') [Formula.Var (string8_string ''x'')]))
            (Formula.Pred (string8_string ''d'') [Formula.Var (string8_string ''x'')]))" *)

(* value "execute_trivial_eval mytrace6 [string8_string ''x''] 1 phi7" *)

(* value "execute_trivial_eval mytrace4 [string8_string ''a'', string8_string ''r''] 3 phi5" *)

(* value "let e = execute_trivial_eval mytrace4 [string8_string ''a'', string8_string ''f''] 0 phi4 in 
       check_all mytrace4 phi4 e" *)

(* Example 2 *)
(* definition mytrace2 :: "string Formula.trace" where 
  "mytrace2 = trace_of_list
     [({(''p'', [''Dmitriy'', ''Traytel'']), (''p'', [''Jonathan'', ''Munive'']),
        (''q'', [''Munive'']), (''q'', [''Lima''])}, 0::nat),
      ({(''p'', [''Leonardo'', ''Lima'']), (''q'', [''Lima''])}, 0::nat)]"

definition phi2 where
  "phi2 = Formula.Exists ''last''
    (Formula.And (Formula.Pred ''p'' [Formula.Var ''first'', Formula.Var ''last''])
       (Formula.Pred ''q'' [Formula.Var ''last'']))"

definition phi3 where
  "phi3 = Formula.Forall ''last'' (Formula.Imp (Formula.Pred ''q'' [Formula.Var ''last''])
    (Formula.Exists ''first'' (Formula.Pred ''p'' [Formula.Var ''first'', Formula.Var ''last''])))"

value "execute_trivial_eval mytrace2 [''first'', ''last''] 0 (Formula.Pred ''p'' [Formula.Var ''first'', Formula.Var ''last''])"
value "execute_trivial_eval mytrace2 [''first'', ''last''] 0 (Formula.Pred ''p'' [Formula.Var ''first'', Formula.Var ''last''])"
value "execute_trivial_eval mytrace2 [''last''] 0 (Formula.Pred ''q'' [Formula.Var ''last''])" 
value "execute_trivial_eval mytrace2 [''first'', ''last''] 1 (Formula.Pred ''p'' [Formula.Var ''first'', Formula.Var ''last''])"
value "execute_trivial_eval mytrace2 [''first'', ''last''] 1 (Formula.Pred ''q'' [Formula.Var ''last''])"
value "execute_trivial_eval mytrace2 [''first'', ''last''] 0 (Formula.And (Formula.Pred ''p'' [Formula.Var ''first'', Formula.Var ''last'']) (Formula.Pred ''q'' [Formula.Var ''last'']))"
value "execute_trivial_eval mytrace2 [''first'', ''last''] 1 (Formula.And (Formula.Pred ''p'' [Formula.Var ''first'', Formula.Var ''last'']) (Formula.Pred ''q'' [Formula.Var ''last'']))"
value "execute_trivial_eval mytrace2 [''first''] 0 phi2"
value "execute_trivial_eval mytrace2 [''first''] 1 phi2"
value "execute_trivial_eval mytrace2 [] 0 phi3"
value "execute_trivial_eval mytrace2 [] 1 phi3" *) 

(* Example 3 *)
(* definition mytrace3 :: "string Formula.trace" where 
  "mytrace3 = trace_of_list
     [({(''p'', [''10''])}, 0::nat),
      ({(''q'', [''20''])}, 1::nat),
      ({(''q'', [''20''])}, 2::nat)]"

definition phi4 where
  "phi4 = Formula.Since (Formula.Pred ''q'' [Formula.Var ''y'']) all (Formula.Exists ''x'' (Formula.Pred ''p'' [Formula.Var ''x'']))"

value "execute_trivial_eval mytrace3 [''y''] 0 phi4" *)
(* value "execute_trivial_eval mytrace3 [''y''] 1 phi4"
value "execute_trivial_eval mytrace3 [''y''] 2 phi4" *)

(* Example 4 *)
(* definition mytrace4 :: "string Formula.trace" where 
  "mytrace4 = trace_of_list
     [({(''mgr_S'', [''Mallory'', ''Alice'']),
        (''mgr_S'', [''Merlin'', ''Bob'']),
        (''mgr_S'', [''Merlin'', ''Charlie''])}, 1307532861::nat),
      ({(''approve'', [''Mallory'', ''152''])}, 1307532861),
      ({(''approve'', [''Merlin'', ''163'']),
        (''publish'', [''Alice'', ''160'']),
        (''mgr_F'', [''Merlin'', ''Charlie''])}, 1307955600),
      ({(''approve'', [''Merlin'', ''187'']),
        (''publish'', [''Bob'', ''163'']),
        (''publish'', [''Alice'', ''163'']),
        (''publish'', [''Charlie'', ''163'']),
        (''publish'', [''Charlie'', ''152''])}, 1308477599)]"

definition phi5 :: "string Formula.formula" where
  "phi5 = Formula.Imp (Formula.Pred ''publish'' [Formula.Var ''a'', Formula.Var ''f''])
    (Formula.Once (init 604800) (Formula.Exists ''m'' (Formula.Since 
      (Formula.Neg (Formula.Pred ''mgr_F'' [Formula.Var ''m'', Formula.Var ''a''])) all
      (Formula.And (Formula.Pred ''mgr_S'' [Formula.Var ''m'', Formula.Var ''a''])
                 (Formula.Pred ''approve'' [Formula.Var ''m'', Formula.Var ''f''])))))" *)

(* value "execute_trivial_eval mytrace4 [''a'', ''f''] 2 phi5" *)

(* Example 5 *)
(* definition mytrace5 :: "string Formula.trace" where 
  "mytrace5 = trace_of_list
     [({(''p'', [''10''])}, 0::nat)]"

definition phi6 where
  "phi6 = Formula.Exists ''x'' (Formula.Pred ''p'' [Formula.Var ''x''])" *)

(* value "execute_trivial_eval mytrace5 [''x''] 0 phi6" *)

end