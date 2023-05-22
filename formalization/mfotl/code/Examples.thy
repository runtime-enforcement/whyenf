theory Examples
  imports Monitor_Code
begin

(* Example 1 *)
definition mytrace :: "nat MFOTL.trace" where 
  "mytrace = trace_of_list [({(''p'', [1::nat])}, 0::nat)]"

value "execute_trivial_eval mytrace [''x''] (0::nat) (MFOTL.Pred ''p'' [MFOTL.Var ''x''] :: nat MFOTL.formula)"

(* Example 2 *)
definition mytrace2 :: "string MFOTL.trace" where 
  "mytrace2 = trace_of_list
     [({(''p'', [''Dmitriy'', ''Traytel'']), (''p'', [''Jonathan'', ''Munive'']),
        (''q'', [''Munive'']), (''q'', [''Lima''])}, 0::nat),
      ({(''p'', [''Leonardo'', ''Lima'']), (''q'', [''Lima''])}, 0::nat)]"

definition phi2 where
  "phi2 = MFOTL.Exists ''last''
    (MFOTL.And (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])
       (MFOTL.Pred ''q'' [MFOTL.Var ''last'']))"

definition phi3 where
  "phi3 = MFOTL.Forall ''last'' (MFOTL.Imp (MFOTL.Pred ''q'' [MFOTL.Var ''last''])
    (MFOTL.Exists ''first'' (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])))"

value "execute_trivial_eval mytrace2 [''first'', ''last''] 0 (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])"
(* value "execute_trivial_eval mytrace2 [''first'', ''last''] 0 (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])"
value "execute_trivial_eval mytrace2 [''last''] 0 (MFOTL.Pred ''q'' [MFOTL.Var ''last''])" 
value "execute_trivial_eval mytrace2 [''first'', ''last''] 1 (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])"
value "execute_trivial_eval mytrace2 [''first'', ''last''] 1 (MFOTL.Pred ''q'' [MFOTL.Var ''last''])"
value "execute_trivial_eval mytrace2 [''first'', ''last''] 0 (MFOTL.And (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last'']) (MFOTL.Pred ''q'' [MFOTL.Var ''last'']))"
value "execute_trivial_eval mytrace2 [''first'', ''last''] 1 (MFOTL.And (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last'']) (MFOTL.Pred ''q'' [MFOTL.Var ''last'']))"
value "execute_trivial_eval mytrace2 [''first''] 0 phi2"
value "execute_trivial_eval mytrace2 [''first''] 1 phi2"
value "execute_trivial_eval mytrace2 [] 0 phi3"
value "execute_trivial_eval mytrace2 [] 1 phi3" *)

(* Example 3 *)
definition mytrace3 :: "string MFOTL.trace" where 
  "mytrace3 = trace_of_list
     [({(''p'', [''10''])}, 0::nat),
      ({(''q'', [''20''])}, 1::nat),
      ({(''q'', [''20''])}, 2::nat)]"

definition phi4 where
  "phi4 = MFOTL.Since (MFOTL.Pred ''q'' [MFOTL.Var ''y'']) all (MFOTL.Exists ''x'' (MFOTL.Pred ''p'' [MFOTL.Var ''x'']))"

value "execute_trivial_eval mytrace3 [''y''] 0 phi4"
(* value "execute_trivial_eval mytrace3 [''y''] 1 phi4"
value "execute_trivial_eval mytrace3 [''y''] 2 phi4" *)

(* Example 4 *)
definition mytrace4 :: "string MFOTL.trace" where 
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

definition phi5 :: "string MFOTL.formula" where
  "phi5 = MFOTL.Imp (MFOTL.Pred ''publish'' [MFOTL.Var ''a'', MFOTL.Var ''f''])
    (MFOTL.Once (init 604800) (MFOTL.Exists ''m'' (MFOTL.Since 
      (MFOTL.Neg (MFOTL.Pred ''mgr_F'' [MFOTL.Var ''m'', MFOTL.Var ''a''])) all
      (MFOTL.And (MFOTL.Pred ''mgr_S'' [MFOTL.Var ''m'', MFOTL.Var ''a''])
                 (MFOTL.Pred ''approve'' [MFOTL.Var ''m'', MFOTL.Var ''f''])))))"

(* value "execute_trivial_eval mytrace4 [''a'', ''f''] 2 phi5" *)

(* Example 5 *)
definition mytrace5 :: "string MFOTL.trace" where 
  "mytrace5 = trace_of_list
     [({(''p'', [''10''])}, 0::nat)]"

definition phi6 where
  "phi6 = MFOTL.Exists ''x'' (MFOTL.Pred ''p'' [MFOTL.Var ''x''])"

(* value "execute_trivial_eval mytrace5 [''x''] 0 phi6" *)

end