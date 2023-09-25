theory Containers_Code
imports Monitor_Code Containers.Containers
begin

subsection \<open>Comparator\<close>

(* This is needed because of primrec requirements *)
context fixes compa :: "'a \<Rightarrow> 'b \<Rightarrow> order" begin

fun comparator_list' :: "'a list \<Rightarrow> 'b list \<Rightarrow> order" where
  "comparator_list' [] [] = Eq"
| "comparator_list' [] (y # ys) = Lt"
| "comparator_list' (x # xs) [] = Gt"
| "comparator_list' (x # xs) (y # ys) = (case compa x y of Eq \<Rightarrow> comparator_list' xs ys | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)"

end

definition comparator_set where
  "comparator_set compa = comp_of_ords (ord.set_less_eq (le_of_comp compa)) (ord.set_less (le_of_comp compa))"

derive ccompare MFOTL.trm

instantiation sproof and vproof :: (ccompare) ccompare 
begin

primrec comparator_sproof :: "('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> 'a sproof \<Rightarrow> 'a sproof \<Rightarrow> order" 
  and comparator_vproof :: "('a \<Rightarrow> 'a \<Rightarrow> order) \<Rightarrow> 'a vproof \<Rightarrow> 'a vproof \<Rightarrow> order" where
  "comparator_sproof compa (STT i) rhs =
    (case rhs of       
      STT i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SPred i r ts) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred i' r' ts' \<Rightarrow> (case comparator_of i i' of
                           Eq \<Rightarrow> (case compare r r' of
                                   Eq \<Rightarrow> comparator_list (comparator_trm compa) ts ts'
                                 | Lt \<Rightarrow> Lt
                                 | Gt \<Rightarrow> Gt)
                         | Lt \<Rightarrow> Lt
                         | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SNeg vp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SOrL sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SOrR sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SAnd sp1 sp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd sp1' sp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of 
                          Eq \<Rightarrow> comparator_sproof compa sp2 sp2' 
                        | Lt \<Rightarrow> Lt 
                        | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SImpL vp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SImpR sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SIffSS sp1 sp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS sp1' sp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of 
                            Eq \<Rightarrow> comparator_sproof compa sp2 sp2' 
                          | Lt \<Rightarrow> Lt
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SIffVV vp1 vp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV vp1' vp2' \<Rightarrow> (case comparator_vproof compa vp1 vp1' of 
                            Eq \<Rightarrow> comparator_vproof compa vp2 vp2'   
                          | Lt \<Rightarrow> Lt 
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SExists x val sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists x' val' sp' \<Rightarrow> (case compare x x' of
                               Eq \<Rightarrow> (case compa val val' of
                                       Eq \<Rightarrow> comparator_sproof compa sp sp'
                                     | Lt \<Rightarrow> Lt
                                     | Gt \<Rightarrow> Gt)
                             | Lt \<Rightarrow> Lt
                             | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SForall x part) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall x' part' \<Rightarrow> (case compare x x' of 
                            Eq \<Rightarrow> comparator_list' (\<lambda>(A,f) (B,x). case comparator_set compa A B of 
                                                                   Eq \<Rightarrow> f x
                                                                 | Lt \<Rightarrow> Lt
                                                                 | Gt \<Rightarrow> Gt)
                                 (subsvals (map_part (comparator_sproof compa) part)) (subsvals part')
                          | Lt \<Rightarrow> Lt
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SPrev sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev sp' \<Rightarrow> comparator_sproof compa sp sp' 
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SNext sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext sp' \<Rightarrow> comparator_sproof compa sp sp' 
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SOnce i sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce i' sp' \<Rightarrow> (case comparator_of i i' of 
                        Eq \<Rightarrow> comparator_sproof compa sp sp' 
                      | Lt \<Rightarrow> Lt 
                      | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SEventually i sp) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually i' sp' \<Rightarrow> (case comparator_of i i' of 
                              Eq \<Rightarrow> comparator_sproof compa sp sp' 
                            | Lt \<Rightarrow> Lt 
                            | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SHistorically i li sps) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually _ _ \<Rightarrow> Gt
    | SHistorically i' li' sps' \<Rightarrow> (case comparator_of i i' of 
                                     Eq \<Rightarrow> (case comparator_of li li' of 
                                             Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_sproof compa) sps) sps'
                                           | Lt \<Rightarrow> Lt 
                                           | Gt \<Rightarrow> Gt)
                                   | Lt \<Rightarrow> Lt 
                                   | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SHistoricallyOut i) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually _ _ \<Rightarrow> Gt
    | SHistorically _ _ _ \<Rightarrow> Gt
    | SHistoricallyOut i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SAlways i hi sps) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually _ _ \<Rightarrow> Gt
    | SHistorically _ _ _ \<Rightarrow> Gt
    | SHistoricallyOut _ \<Rightarrow> Gt
    | SAlways i' hi' sps' \<Rightarrow> (case comparator_of i i' of 
                               Eq \<Rightarrow> (case comparator_of hi hi' of 
                                       Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_sproof compa) sps) sps'
                                     | Lt \<Rightarrow> Lt 
                                     | Gt \<Rightarrow> Gt)
                             | Lt \<Rightarrow> Lt 
                             | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SSince sp2 sp1s) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually _ _ \<Rightarrow> Gt
    | SHistorically _ _ _ \<Rightarrow> Gt
    | SHistoricallyOut _ \<Rightarrow> Gt
    | SAlways _ _ _ \<Rightarrow> Gt
    | SSince sp2' sp1s' \<Rightarrow> (case comparator_sproof compa sp2 sp2' of 
                             Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_sproof compa) sp1s) sp1s'
                           | Lt \<Rightarrow> Lt 
                           | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_sproof compa (SUntil sp1s sp2) rhs =
    (case rhs of
      STT _ \<Rightarrow> Gt
    | SPred _ _ _ \<Rightarrow> Gt
    | SNeg _ \<Rightarrow> Gt
    | SOrL _ \<Rightarrow> Gt
    | SOrR _ \<Rightarrow> Gt
    | SAnd _ _ \<Rightarrow> Gt
    | SImpL _ \<Rightarrow> Gt
    | SImpR _ \<Rightarrow> Gt
    | SIffSS _ _ \<Rightarrow> Gt
    | SIffVV _ _ \<Rightarrow> Gt
    | SExists _ _ _ \<Rightarrow> Gt
    | SForall _ _ \<Rightarrow> Gt
    | SPrev _ \<Rightarrow> Gt
    | SNext _ \<Rightarrow> Gt
    | SOnce _ _ \<Rightarrow> Gt
    | SEventually _ _ \<Rightarrow> Gt
    | SHistorically _ _ _ \<Rightarrow> Gt
    | SHistoricallyOut _ \<Rightarrow> Gt
    | SAlways _ _ _ \<Rightarrow> Gt
    | SSince _ _ \<Rightarrow> Gt
    | SUntil sp1s' sp2' \<Rightarrow> (case comparator_sproof compa sp2 sp2' of 
                             Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_sproof compa) sp1s) sp1s'
                           | Lt \<Rightarrow> Lt 
                           | Gt \<Rightarrow> Gt))"
| "comparator_vproof compa (VFF i) rhs =
    (case rhs of
      VFF i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VPred i r ts) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred i' r' ts' \<Rightarrow> (case comparator_of i i' of
                           Eq \<Rightarrow> (case compare r r' of
                                   Eq \<Rightarrow> comparator_list (comparator_trm compa) ts ts'
                                 | Lt \<Rightarrow> Lt
                                 | Gt \<Rightarrow> Gt)
                         | Lt \<Rightarrow> Lt
                         | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VNeg sp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg sp' \<Rightarrow> comparator_sproof compa sp sp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VOr vp1 vp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr vp1' vp2' \<Rightarrow> (case comparator_vproof compa vp1 vp1' of 
                         Eq \<Rightarrow> comparator_vproof compa vp2 vp2' 
                       | Lt \<Rightarrow> Lt 
                       | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VAndL vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VAndR vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VImp sp1 vp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp sp1' vp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of 
                          Eq \<Rightarrow> comparator_vproof compa vp2 vp2' 
                        | Lt \<Rightarrow> Lt 
                        | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VIffSV sp1 vp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV sp1' vp2' \<Rightarrow> (case comparator_sproof compa sp1 sp1' of 
                            Eq \<Rightarrow> comparator_vproof compa vp2 vp2' 
                          | Lt \<Rightarrow> Lt 
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VIffVS vp1 sp2) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS vp1' sp2' \<Rightarrow> (case comparator_vproof compa vp1 vp1' of 
                            Eq \<Rightarrow> comparator_sproof compa sp2 sp2' 
                          | Lt \<Rightarrow> Lt 
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VExists x part) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists x' part' \<Rightarrow> (case compare x x' of 
                            Eq \<Rightarrow> comparator_list' (\<lambda>(A,f) (B,x). case comparator_set compa A B of 
                                                                   Eq \<Rightarrow> f x
                                                                 | Lt \<Rightarrow> Lt
                                                                 | Gt \<Rightarrow> Gt)
                                 (subsvals (map_part (comparator_vproof compa) part)) (subsvals part')
                          | Lt \<Rightarrow> Lt
                          | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VForall x val vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall x' val' vp' \<Rightarrow> (case compare x x' of
                               Eq \<Rightarrow> (case compa val val' of
                                       Eq \<Rightarrow> comparator_vproof compa vp vp'
                                     | Lt \<Rightarrow> Lt
                                     | Gt \<Rightarrow> Gt)
                             | Lt \<Rightarrow> Lt
                             | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VPrev vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa VPrevZ rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Eq
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VPrevOutL i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VPrevOutR i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VNext vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext vp' \<Rightarrow> comparator_vproof compa vp vp'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VNextOutL i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VNextOutR i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VOnceOut i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VOnce i li vps) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce i' li' vps' \<Rightarrow> (case comparator_of i i' of 
                             Eq \<Rightarrow> (case comparator_of li li' of 
                                     Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vps) vps' 
                                   | Lt \<Rightarrow> Lt 
                                   | Gt \<Rightarrow> Gt)
                           | Lt \<Rightarrow> Lt 
                           | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VEventually i hi vps) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually i' hi' vps' \<Rightarrow> (case comparator_of i i' of 
                                   Eq \<Rightarrow> (case comparator_of hi hi' of 
                                           Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vps) vps'
                                         | Lt \<Rightarrow> Lt 
                                         | Gt \<Rightarrow> Gt)
                                 | Lt \<Rightarrow> Lt 
                                 | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VHistorically i vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically i' vp' \<Rightarrow> (case comparator_of i i' of 
                                Eq \<Rightarrow> comparator_vproof compa vp vp' 
                              | Lt \<Rightarrow> Lt 
                              | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VAlways i vp) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways i' vp' \<Rightarrow> (case comparator_of i i' of 
                          Eq \<Rightarrow> comparator_vproof compa vp vp' 
                        | Lt \<Rightarrow> Lt 
                        | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VSinceOut i) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways _ _ \<Rightarrow> Gt
    | VSinceOut i' \<Rightarrow> comparator_of i i'
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VSince i vp1 vp2s) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways _ _ \<Rightarrow> Gt
    | VSinceOut _ \<Rightarrow> Gt
    | VSince i' vp1' vp2s' \<Rightarrow> (case comparator_of i i' of 
                                Eq \<Rightarrow> (case comparator_vproof compa vp1 vp1' of
                                        Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s'
                                      | Lt \<Rightarrow> Lt 
                                      | Gt \<Rightarrow> Gt)
                              | Lt \<Rightarrow> Lt 
                              | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VSinceInf i li vp2s) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways _ _ \<Rightarrow> Gt
    | VSinceOut _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VSinceInf i' li' vp2s' \<Rightarrow> (case comparator_of i i' of 
                                  Eq \<Rightarrow> (case comparator_of li li' of 
                                          Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s'
                                        | Lt \<Rightarrow> Lt 
                                        | Gt \<Rightarrow> Gt)
                                | Lt \<Rightarrow> Lt 
                                | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VUntil i vp2s vp1) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways _ _ \<Rightarrow> Gt
    | VSinceOut _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VSinceInf _ _ _ \<Rightarrow> Gt
    | VUntil i' vp2s' vp1' \<Rightarrow> (case comparator_of i i' of 
                                Eq \<Rightarrow> (case comparator_vproof compa vp1 vp1' of
                                        Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s'
                                      | Lt \<Rightarrow> Lt 
                                      | Gt \<Rightarrow> Gt)
                              | Lt \<Rightarrow> Lt 
                              | Gt \<Rightarrow> Gt)
    | _ \<Rightarrow> Lt)"
| "comparator_vproof compa (VUntilInf i hi vp2s) rhs =
    (case rhs of
      VFF _ \<Rightarrow> Gt
    | VPred _ _ _ \<Rightarrow> Gt
    | VNeg _ \<Rightarrow> Gt
    | VOr _ _ \<Rightarrow> Gt
    | VAndL _ \<Rightarrow> Gt
    | VAndR _ \<Rightarrow> Gt
    | VImp _ _ \<Rightarrow> Gt
    | VIffSV _ _ \<Rightarrow> Gt
    | VIffVS _ _ \<Rightarrow> Gt
    | VExists _ _ \<Rightarrow> Gt
    | VForall _ _ _ \<Rightarrow> Gt
    | VPrev _ \<Rightarrow> Gt
    | VPrevZ \<Rightarrow> Gt
    | VPrevOutL _ \<Rightarrow> Gt
    | VPrevOutR _ \<Rightarrow> Gt
    | VNext _ \<Rightarrow> Gt
    | VNextOutL _ \<Rightarrow> Gt
    | VNextOutR _ \<Rightarrow> Gt
    | VOnceOut _ \<Rightarrow> Gt
    | VOnce _ _ _ \<Rightarrow> Gt
    | VEventually _ _ _ \<Rightarrow> Gt
    | VHistorically _ _ \<Rightarrow> Gt
    | VAlways _ _ \<Rightarrow> Gt
    | VSinceOut _ \<Rightarrow> Gt
    | VSince _ _ _ \<Rightarrow> Gt
    | VSinceInf _ _ _ \<Rightarrow> Gt
    | VUntil _ _ _ \<Rightarrow> Gt
    | VUntilInf i' hi' vp2s' \<Rightarrow> (case comparator_of i i' of 
                                  Eq \<Rightarrow> (case comparator_of hi hi' of 
                                          Eq \<Rightarrow> comparator_list' (\<lambda>f x. f x) (map (comparator_vproof compa) vp2s) vp2s'
                                        | Lt \<Rightarrow> Lt 
                                        | Gt \<Rightarrow> Gt)
                                | Lt \<Rightarrow> Lt 
                                | Gt \<Rightarrow> Gt))"


definition "ccompare_sproof = (case ID ccompare of None \<Rightarrow> None | Some comp_'a \<Rightarrow> Some (comparator_sproof comp_'a))"
definition "ccompare_vproof = (case ID ccompare of None \<Rightarrow> None | Some comp_'a \<Rightarrow> Some (comparator_vproof comp_'a))"

lemma comparator_list'_map[simp]: "comparator_list' (\<lambda>f x. f x) (map f xs) ys = comparator_list f xs ys"
  by (induct xs ys rule: comparator_list'.induct[where compa = f]) (auto split: order.splits)

lemma comparator_list'_map2[simp]: "comparator_list' (\<lambda>(A,f) (B,x). case comparator_set compa A B of Eq \<Rightarrow> f x | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt) (map (map_prod id f) xs) ys = comparator_list (comparator_prod (comparator_set compa) f) xs ys"
  by (induct xs ys rule: comparator_list'.induct[where compa = "(comparator_prod (comparator_set compa) f)"]) (auto split: order.splits)

lemma comparator_list'_vals_map_part [simp]: "subsvals (map_part f part) = map (map_prod id f) (subsvals part)"
  apply transfer
  apply auto
  done

lemma comparator_set: "comparator compa \<Longrightarrow> comparator (comparator_set compa)"
  by (auto simp: comparator_set_def intro!: comp_of_ords linorder.set_less_eq_linorder comparator.linorder)

lemma comparator_list_alt: 
  "comparator_list compa xs ys = Eq \<longleftrightarrow> list_all2 (\<lambda>x y. compa x y = Eq) xs ys"
  by (induct xs ys rule: comparator_list'.induct[of _ compa]) (auto split: order.splits)

lemma comparator_prod_alt: 
  "comparator_prod compa compb ab cd = Eq \<longleftrightarrow> rel_prod (\<lambda>x y. compa x y = Eq) (\<lambda>x y. compb x y = Eq) ab cd"
  by (cases ab; cases cd) (auto split: order.splits)

lemma comparator_set_alt: 
  "comparator compa \<Longrightarrow> comparator_set compa X Y = Eq \<longleftrightarrow> rel_set (\<lambda>x y. compa x y = Eq) X Y"
  using comparator.eq_Eq_conv[of compa] comparator.eq_Eq_conv[OF comparator_set, of compa]
  by (auto simp: rel_set_eq)

lemma subsvals_inject[simp]: "subsvals xs = subsvals ys \<longleftrightarrow> xs = ys"
  by transfer auto

lemma subsvals_ValsD: "(X, p) \<in> set (subsvals part) \<Longrightarrow> p \<in> Vals part"
  by transfer (force simp: prod_set_defs)

lemma eq_Eq_comparator_proof:
  assumes "ID ccompare = Some compa"
  shows "(comparator_sproof compa sp sp' = Eq) \<longleftrightarrow> (sp = sp')"
    "(comparator_vproof compa vp vp' = Eq) \<longleftrightarrow> (vp = vp')"
proof (induction sp and vp arbitrary: sp' and vp')
  case (STT x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SPred x1 x2 x3)
  then show ?case
    by (auto simp add: comparator_of_def comparator.eq_Eq_conv ID_ccompare' assms comparator_list comparator_trm 
        split: sproof.splits order.splits)
next
  case (SNeg x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrL x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrR x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAnd x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply force
    done
next
  case (SImpL x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SImpR x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SIffSS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply force
    done
next
  case (SIffVV x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply force
    done
next
  case (SExists x1 x2 x3)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis ID_code assms ccompare comparator.eq_Eq_conv compare_refl order.distinct(1,3))
    done
next
  case (SForall x part)
  then show ?case
    using ID_ccompare'[OF assms]
    by (auto simp add: comparator_of_def rel_set_eq prod.rel_eq list.rel_eq
      comparator_list_alt comparator_prod_alt comparator_set_alt
      comparator.eq_Eq_conv[OF ID_ccompare'[OF assms]]
      dest: list.rel_cong[OF refl refl prod.rel_cong[OF refl refl, of _ _ _ "(=)" _ "(=)"], of _ _ "\<lambda>x y. x" "\<lambda>x y. y" "\<lambda>x y. R" "\<lambda>x y. S" for R S, THEN iffD1, rotated -1]
      intro: list.rel_cong[OF refl refl prod.rel_cong[OF refl refl, of _ _ _ "(=)" _ "(=)"], of _ _ "\<lambda>x y. x" "\<lambda>x y. y" "\<lambda>x y. R" "\<lambda>x y. S" for R S, THEN iffD2]
      dest!: subsvals_ValsD split: sproof.splits order.splits)
next
  case (SPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SNext x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOnce x1 x2)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SEventually x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SHistorically x1 x2 x3)
  then show ?case
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SHistoricallyOut x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAlways x1 x2 x3)
  then show ?case
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SSince x1 x2)
  then show ?case
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis order.distinct(1) order.distinct(3))
    done
next
  case (SUntil x1 x2)
  then show ?case
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis order.distinct(1) order.distinct(3))
    done
next
  case (VFF x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPred x1 x2 x3)
  then show ?case
    by (auto simp add: comparator_of_def comparator.eq_Eq_conv ID_ccompare' assms comparator_list comparator_trm 
        split: vproof.splits order.splits)
next
  case (VNeg x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOr x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply force
    done
next
  case (VAndL x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAndR x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VImp x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply force
    done
next
  case (VIffSV x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply force
    done
next
  case (VIffVS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply force
    done
next
  case (VExists x1 x2)
  then show ?case
    using ID_ccompare'[OF assms]
    by (auto simp add: comparator_of_def rel_set_eq prod.rel_eq list.rel_eq
      comparator_list_alt comparator_prod_alt comparator_set_alt
      comparator.eq_Eq_conv[OF ID_ccompare'[OF assms]]
      dest: list.rel_cong[OF refl refl prod.rel_cong[OF refl refl, of _ _ _ "(=)" _ "(=)"], of _ _ "\<lambda>x y. x" "\<lambda>x y. y" "\<lambda>x y. R" "\<lambda>x y. S" for R S, THEN iffD1, rotated -1]
      intro: list.rel_cong[OF refl refl prod.rel_cong[OF refl refl, of _ _ _ "(=)" _ "(=)"], of _ _ "\<lambda>x y. x" "\<lambda>x y. y" "\<lambda>x y. R" "\<lambda>x y. S" for R S, THEN iffD2]
      dest!: subsvals_ValsD split: vproof.splits order.splits)
next
  case (VForall x1 x2 x3)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (metis ID_code assms ccompare comparator.eq_Eq_conv compare_refl order.distinct(1) order.distinct(3))
    done
next
  case (VPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case VPrevZ
  then show ?case 
    by (simp split: vproof.splits)
next
  case (VPrevOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPrevOutR x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNext x)
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnce x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VEventually x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VHistorically x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAlways x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSinceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSince x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.split order.splits)
    apply (metis order.distinct(1) order.distinct(3))
    done
next
  case (VSinceInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.split order.splits)
next
  case (VUntil x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.split order.splits)
    apply (metis order.distinct(1) order.distinct(3))
    done
next
  case (VUntilInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(1)[unfolded peq_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.split order.splits)
qed

lemma invert_order_comperator_list:
  "\<forall>x \<in> set xs. \<forall>y. invert_order (compa x y) = compa y x \<Longrightarrow> invert_order (comparator_list compa xs ys) = comparator_list compa ys xs"
  apply (induct xs ys rule: comparator_list'.induct[of _ compa])
     apply (auto split: order.splits)
       apply (metis invert_order.simps(3) order.distinct(1))
      apply (metis invert_order.simps(2,3) order.distinct(1))
     apply (metis invert_order.simps(1,2,3) order.distinct(1))
    apply (metis invert_order.simps(1) order.distinct(5))
   apply (metis invert_order.simps(2) order.distinct(1))
  apply (metis invert_order.simps(2) order.distinct(5))
  done

lemma invert_order_comparator_proof:
  assumes "ID ccompare = Some compa"
  shows "invert_order (comparator_sproof compa sp sp') = comparator_sproof compa sp' sp"
    "invert_order (comparator_vproof compa vp vp') = comparator_vproof compa vp' vp"
proof(induct sp and vp arbitrary: sp' and vp')
  case (STT x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SPred x1 x2 x3)
  then show ?case
    using assms
    apply (auto simp add: comparator_of_def ID_ccompare' comparator.sym comparator_list comparator_trm split: sproof.splits order.splits)
     apply (metis comparator_compare comparator_def compare_refl order.distinct(1))
    apply (metis comparator.sym comparator_compare invert_order.simps(2) order.distinct(5))
    done
next
  case (SNeg x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrL x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrR x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAnd x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (SImpL x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SImpR x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SIffSS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (SIffVV x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (SExists x1 x2 x3)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (verit) assms ccomp_comparator comparator.sym comparator_compare invert_order.simps(1-3) option.sel option.simps(3) order.simps(6))
    done
next
  case (SForall x part)
  then show ?case
    apply (auto simp add: comparator_of_def
        comparator.eq_Eq_conv[OF comparator_set[OF ID_ccompare'[OF assms]]]
        comparator.comp_same[OF comparator_set[OF ID_ccompare'[OF assms]]]
        dest!: subsvals_ValsD
        intro!: invert_order_comperator_list split: sproof.splits order.splits)
       apply (metis assms ccomp_comparator comparator.sym comparator_set invert_order.simps(1) option.sel option.simps(3) order.distinct(5))
      apply (metis assms ccomp_comparator comparator.sym comparator_set invert_order.simps(2) option.sel option.simps(3) order.distinct(5))
     apply (metis comparator.eq_Eq_conv comparator_bool.simps(2) comparator_compare comparator_def compare_bool_def)
    apply (metis comparator_compare comparator_def invert_order.simps(2) order.distinct(5))
    done
next
  case (SPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SNext x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOnce x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SEventually x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SHistorically x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits order.splits)
next
  case (SHistoricallyOut x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAlways x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits order.splits)
next
  case (SSince x1 x2)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits if_splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (SUntil x1 x2)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits if_splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VFF x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPred x1 x2 x3)
  then show ?case 
    using assms
    apply (auto simp add: comparator_of_def ID_ccompare' comparator.sym comparator_list comparator_trm split: vproof.splits order.splits)
     apply (metis comparator_compare comparator_def compare_refl order.distinct(1))
    apply (metis comparator.sym comparator_compare invert_order.simps(2) order.distinct(5))
    done
next
  case (VNeg x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOr x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VAndL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAndR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VImp x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VIffSV x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VIffVS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VExists x1 x2)
  then show ?case
    apply (auto simp add: comparator_of_def
        comparator.eq_Eq_conv[OF comparator_set[OF ID_ccompare'[OF assms]]]
        comparator.comp_same[OF comparator_set[OF ID_ccompare'[OF assms]]]
        dest!: subsvals_ValsD
        intro!: invert_order_comperator_list split: vproof.splits order.splits)
       apply (metis assms ccomp_comparator comparator.sym comparator_set invert_order.simps(1) option.sel option.simps(3) order.distinct(5))
      apply (metis assms ccomp_comparator comparator.sym comparator_set invert_order.simps(2) option.sel option.simps(3) order.distinct(5))
     apply (metis comparator.eq_Eq_conv comparator_bool.simps(2) comparator_compare comparator_def compare_bool_def)
    apply (metis comparator_compare comparator_def invert_order.simps(2) order.distinct(5))
    done
next
  case (VForall x1 x2 x3)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (verit) assms ccomp_comparator comparator.sym comparator_compare invert_order.simps(1-3) option.sel option.simps(3) order.simps(6))
    done
next
  case (VPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case VPrevZ
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPrevOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPrevOutR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNext x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnce x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VEventually x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VHistorically x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAlways x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSinceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSince x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.splits order.splits if_splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VSinceInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VUntil x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.splits order.splits if_splits)
    apply (metis invert_order.simps(1-3) order.simps(6))
    done
next
  case (VUntilInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(2)[unfolded psym_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
qed

lemma trans_order_equal[simp]:
  "trans_order Eq b b"
  "trans_order b Eq b"
  by (intro trans_orderI, auto)+

declare trans_order_different[simp]

lemma trans_order_comperator_list:
  "\<forall>x \<in> set xs. \<forall>y z. trans_order (compa x y) (compa y z) (compa x z) \<Longrightarrow> trans_order (comparator_list compa xs ys) (comparator_list compa ys zs) (comparator_list compa xs zs)"
  apply (induct xs arbitrary: ys zs)
  subgoal for ys zs
    by (cases ys; cases zs) simp_all
  subgoal for x xs ys zs
    apply (cases ys; cases zs)
       apply (auto split: order.splits)
          apply (metis order.simps(4) trans_order_def)
         apply (metis order.simps(2,4) trans_order_def)
        apply (metis order.simps(4) trans_order_def)
       apply (metis order.simps(2,4) trans_order_def)
      apply (metis order.simps(4) trans_order_def)
     apply (metis order.simps(2) trans_order_def)
    apply (metis)
    done
  done

lemma trans_comparator_proof:
  assumes "ID ccompare = Some compa"
  shows "trans_order (comparator_sproof compa sp sp') (comparator_sproof compa sp' sp'') (comparator_sproof compa sp sp'')"
    "trans_order (comparator_vproof compa vp vp') (comparator_vproof compa vp' vp'') (comparator_vproof compa vp vp'')"
proof (induct sp and vp arbitrary: sp' sp'' and vp' vp'')
  case (STT x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SPred x1 x2 x3)
  then show ?case 
    using assms
    apply (auto simp add: comparator_of_def comparator.eq_Eq_conv ID_ccompare' assms comparator_list comparator_trm split: sproof.splits order.splits)
      apply (smt (verit, best) assms ccomp_comparator comparator.comp_trans comparator.weak_eq comparator_list comparator_trm invert_order.elims option.sel option.simps(3) trans_order_def)
     apply (metis comparator.sym comparator_compare invert_order.simps(1) order.distinct(5))
    apply (metis comparator.comp_trans comparator_compare order.distinct(5))
    done
next
  case (SNeg x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrL x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOrR x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAnd x1 x2)
  then show ?case
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (SImpL x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SImpR x)
  then show ?case
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SIffSS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (SIffVV x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (SExists x1 x2 x3)
  then show ?case
    apply (simp add: comparator_of_def
        comparator.comp_same[OF ID_ccompare'[OF assms]]
        comparator.eq_Eq_conv[OF ID_ccompare'[OF assms]] split: sproof.splits order.splits)
    apply safe
                        apply (simp_all add: 
        comparator.comp_same[OF ID_ccompare'[OF assms]]
        comparator.eq_Eq_conv[OF ID_ccompare'[OF assms]])
                        apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
                        apply (metis comparator.comp_trans comparator_compare order.simps(6))
                        apply (metis comparator.comp_trans comparator_compare order.simps(6))
                        apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
                        apply (metis comparator.comp_trans comparator_compare order.simps(6))
                        apply (metis ID_ccompare' assms comparator_def invert_order.simps(1) order.simps(6))
                        apply (metis ID_ccompare' assms comparator_def order.simps(6))
                        apply (metis comparator.comp_trans comparator_compare order.simps(6))
                        apply (metis ID_ccompare' assms comparator_def invert_order.simps(1) order.simps(6))
                        apply (metis comparator.comp_trans comparator_compare order.simps(6))
                       apply (metis comparator.comp_trans comparator_compare order.simps(6))
                      apply (metis ID_ccompare' assms comparator_def order.simps(6))
                     apply (metis comparator.comp_trans comparator_compare order.simps(6))
                    apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
                   apply (metis comparator.comp_trans comparator_compare order.simps(6))
                  apply (metis comparator.comp_trans comparator_compare order.simps(6))
                 apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
                apply (metis comparator.comp_trans comparator_compare order.simps(6))
               apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
              apply (metis comparator.comp_trans comparator_compare order.simps(6))
             apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
            apply (metis comparator.comp_trans comparator_compare order.simps(6))
           apply (metis comparator.comp_trans comparator_compare order.simps(6))
          apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
         apply (metis comparator.comp_trans comparator_compare order.simps(6))
        apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
       apply (metis comparator.comp_trans comparator_compare order.simps(6))
      apply (metis comparator.comp_trans comparator_compare order.simps(6))
     apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
    apply (metis comparator.comp_trans comparator_compare order.simps(6))
    done
next
  case (SForall x part)
  then show ?case
    apply (auto simp: comparator_of_def
        comparator.eq_Eq_conv[OF comparator_set[OF ID_ccompare'[OF assms]]]
        comparator.comp_same[OF comparator_set[OF ID_ccompare'[OF assms]]]
        intro!: trans_order_comperator_list dest!: subsvals_ValsD split: sproof.splits order.splits)
        apply (metis assms ccomp_comparator comparator.sym comparator_set invert_order.simps(1) option.sel option.simps(3) order.distinct(5))
       apply (metis assms ccomp_comparator comparator.sym comparator_set invert_order.simps(2) option.sel option.simps(3) order.distinct(5))
      apply (metis assms ccomp_comparator comparator.comp_trans comparator_set option.sel option.simps(3) order.simps(6))
     apply (metis comparator.eq_Eq_conv comparator_bool.simps(2) comparator_compare comparator_def compare_bool_def)
    apply (metis comparator_compare comparator_def order.distinct(5))
    done
next
  case (SPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SNext x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SOnce x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SEventually x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SHistorically x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits order.splits)
next
  case (SHistoricallyOut x)
  then show ?case 
    by (simp add: comparator_of_def split: sproof.splits)
next
  case (SAlways x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_sproof compa"]
    by (simp add: comparator_of_def split: sproof.splits order.splits)
next
  case (SSince x1 x2)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (verit) order.distinct(1,3) trans_order_def)
    done
next
  case (SUntil x1 x2)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_sproof compa"]
    apply (simp add: comparator_of_def split: sproof.splits order.splits)
    apply (smt (verit) order.distinct(1,3) trans_order_def)
    done
next
  case (VFF x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPred x1 x2 x3)
  then show ?case 
    using assms
    apply (auto simp add: comparator_of_def comparator.eq_Eq_conv ID_ccompare' assms comparator_list comparator_trm split: vproof.splits order.splits)
      apply (smt (verit, best) assms ccomp_comparator comparator.comp_trans comparator.weak_eq comparator_list comparator_trm invert_order.elims option.sel option.simps(3) trans_order_def)
     apply (metis comparator.sym comparator_compare invert_order.simps(1) order.distinct(5))
    apply (metis comparator.comp_trans comparator_compare order.distinct(5))
    done
next
  case (VNeg x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOr x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (VAndL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAndR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VImp x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (VIffSV x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (VIffVS x1 x2)
  then show ?case 
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (z3) order.simps(2,4) trans_order_def)
    done
next
  case (VExists x part)
  then show ?case
    apply (auto simp: comparator_of_def
        comparator.eq_Eq_conv[OF comparator_set[OF ID_ccompare'[OF assms]]]
        comparator.comp_same[OF comparator_set[OF ID_ccompare'[OF assms]]]
        intro!: trans_order_comperator_list dest!: subsvals_ValsD split: vproof.splits order.splits)
        apply (metis assms ccomp_comparator comparator.sym comparator_set invert_order.simps(1) option.sel option.simps(3) order.distinct(5))
       apply (metis assms ccomp_comparator comparator.sym comparator_set invert_order.simps(2) option.sel option.simps(3) order.distinct(5))
      apply (metis assms ccomp_comparator comparator.comp_trans comparator_set option.sel option.simps(3) order.simps(6))
     apply (metis comparator.eq_Eq_conv comparator_bool.simps(2) comparator_compare comparator_def compare_bool_def)
    apply (metis comparator_compare comparator_def order.distinct(5))
    done
next
  case (VForall x1 x2 x3)
  then show ?case
    apply (simp add: comparator_of_def
        comparator.comp_same[OF ID_ccompare'[OF assms]]
        comparator.eq_Eq_conv[OF ID_ccompare'[OF assms]] split: vproof.splits order.splits)
    apply safe
                        apply (simp_all add: 
        comparator.comp_same[OF ID_ccompare'[OF assms]]
        comparator.eq_Eq_conv[OF ID_ccompare'[OF assms]])
                        apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
                        apply (metis comparator.comp_trans comparator_compare order.simps(6))
                        apply (metis comparator.comp_trans comparator_compare order.simps(6))
                        apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
                        apply (metis comparator.comp_trans comparator_compare order.simps(6))
                        apply (metis ID_ccompare' assms comparator_def invert_order.simps(1) order.simps(6))
                        apply (metis ID_ccompare' assms comparator_def order.simps(6))
                        apply (metis comparator.comp_trans comparator_compare order.simps(6))
                        apply (metis ID_ccompare' assms comparator_def invert_order.simps(1) order.simps(6))
                        apply (metis comparator.comp_trans comparator_compare order.simps(6))
                       apply (metis comparator.comp_trans comparator_compare order.simps(6))
                      apply (metis ID_ccompare' assms comparator_def order.simps(6))
                     apply (metis comparator.comp_trans comparator_compare order.simps(6))
                    apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
                   apply (metis comparator.comp_trans comparator_compare order.simps(6))
                  apply (metis comparator.comp_trans comparator_compare order.simps(6))
                 apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
                apply (metis comparator.comp_trans comparator_compare order.simps(6))
               apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
              apply (metis comparator.comp_trans comparator_compare order.simps(6))
             apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
            apply (metis comparator.comp_trans comparator_compare order.simps(6))
           apply (metis comparator.comp_trans comparator_compare order.simps(6))
          apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
         apply (metis comparator.comp_trans comparator_compare order.simps(6))
        apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
       apply (metis comparator.comp_trans comparator_compare order.simps(6))
      apply (metis comparator.comp_trans comparator_compare order.simps(6))
     apply (metis comparator.sym comparator_compare invert_order.simps(1) order.simps(6))
    apply (metis comparator.comp_trans comparator_compare order.simps(6))
    done
next
  case (VPrev x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case VPrevZ
  then show ?case
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPrevOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VPrevOutR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNext x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutL x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VNextOutR x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VOnce x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VEventually x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VHistorically x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VAlways x1 x2)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSinceOut x)
  then show ?case 
    by (simp add: comparator_of_def split: vproof.splits)
next
  case (VSince x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (verit) order.distinct(1,3) trans_order_def)
    done
next
  case (VSinceInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
next
  case (VUntil x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    apply (simp add: comparator_of_def split: vproof.splits order.splits)
    apply (smt (verit) order.distinct(1,3) trans_order_def)
    done
next
  case (VUntilInf x1 x2 x3)
  then show ?case 
    using comparator_list_pointwise(3)[unfolded ptrans_comp_def, of _ "comparator_vproof compa"]
    by (simp add: comparator_of_def split: vproof.splits order.splits)
qed


instance
   apply standard
   apply (force simp add: ccompare_sproof_def ccompare_vproof_def comparator_def
      eq_Eq_comparator_proof invert_order_comparator_proof intro: trans_comparator_proof[THEN trans_orderD(2)] split: option.splits)+
  done

end

instantiation part :: (type, type) equal begin

lift_definition equal_part :: "('a, 'b) part \<Rightarrow> ('a, 'b) part \<Rightarrow> bool" is "(=)" .

instance proof qed (simp add: equal_part_def Rep_part_inject)

end

derive (eq) ceq part
derive (eq) ceq sproof
derive (rbt) set_impl sproof
derive (eq) ceq vproof
derive (rbt) set_impl vproof

instantiation enat :: ccompare begin
definition ccompare_enat :: "enat comparator option" where
  "ccompare_enat = Some (\<lambda>x y. if x = y then order.Eq else if x < y then order.Lt else order.Gt)"

instance by intro_classes
    (auto simp: ccompare_enat_def split: if_splits intro!: comparator.intro)
end

derive (eq) ceq enat

instantiation enat :: set_impl begin
definition set_impl_enat :: "(enat, set_impl) phantom" where
  "set_impl_enat = phantom set_RBT"

instance ..
end

definition [code del]: "comparator_sproof' = comparator_sproof ccomp"
definition [code del]: "comparator_vproof' = comparator_vproof ccomp"
definition comparator_set' :: "'a :: ccompare set \<Rightarrow> 'a set \<Rightarrow> order" where [code del]: "comparator_set' = comparator_set ccomp"

lemma comparator_set'_code[code]:
  "(comparator_set' :: 'a :: ccompare set \<Rightarrow> 'a set \<Rightarrow> order) =
   (case ID CCOMPARE('a) of None \<Rightarrow> Code.abort STR ''comparator_set: ccompare = None'' (\<lambda>_. comparator_set') | _ \<Rightarrow> ccomp)"
  unfolding comparator_set'_def comparator_set_def cless_eq_set_def cless_set_def ccompare_set_def
  by (auto simp: ID_Some split: option.splits)

lemmas comparator_sproof'_code[code] =
   comparator_sproof.simps[of ccomp, unfolded comparator_list'_map2 comparator_list'_map comparator_list'_vals_map_part,
     folded comparator_sproof'_def comparator_vproof'_def comparator_set'_def]
lemmas comparator_vproof'_code[code] =
   comparator_vproof.simps[of ccomp, unfolded comparator_list'_map2 comparator_list'_map comparator_list'_vals_map_part,
     folded comparator_sproof'_def comparator_vproof'_def comparator_set'_def]

lemma ccompare_sproof_code[code]: "CCOMPARE('a::ccompare sproof) = (case ID CCOMPARE('a) of None \<Rightarrow> None | Some comp_'a \<Rightarrow> Some comparator_sproof')"
  by (auto simp: ccompare_sproof_def comparator_sproof'_def split: option.splits)
lemma ccompare_vproof_code[code]: "CCOMPARE('a::ccompare vproof) = (case ID CCOMPARE('a) of None \<Rightarrow> None | Some comp_'a \<Rightarrow> Some comparator_vproof')"
  by (auto simp: ccompare_vproof_def comparator_vproof'_def split: option.splits)

derive (no) ceq MFOTL.trm
derive (monad) set_impl MFOTL.trm
derive (no) ceq MFOTL.formula
derive (no) ccompare MFOTL.formula
derive (monad) set_impl MFOTL.formula

value "execute_trivial_eval mytrace2 [''first'', ''last''] 0 (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])"
value "execute_trivial_eval mytrace2 [''first'', ''last''] 0 (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])"
value "execute_trivial_eval mytrace2 [''last''] 0 (MFOTL.Pred ''q'' [MFOTL.Var ''last''])" 
value "execute_trivial_eval mytrace2 [''first'', ''last''] 1 (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last''])"
value "execute_trivial_eval mytrace2 [''first'', ''last''] 1 (MFOTL.Pred ''q'' [MFOTL.Var ''last''])"
value "execute_trivial_eval mytrace2 [''first'', ''last''] 0 (MFOTL.And (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last'']) (MFOTL.Pred ''q'' [MFOTL.Var ''last'']))"
value "execute_trivial_eval mytrace2 [''first'', ''last''] 1 (MFOTL.And (MFOTL.Pred ''p'' [MFOTL.Var ''first'', MFOTL.Var ''last'']) (MFOTL.Pred ''q'' [MFOTL.Var ''last'']))"
value "execute_trivial_eval mytrace2 [''first''] 0 phi2"
value "execute_trivial_eval mytrace2 [''first''] 1 phi2"
value "execute_trivial_eval mytrace2 [] 0 phi3"
value "execute_trivial_eval mytrace2 [] 1 phi3"

value "execute_trivial_eval mytrace3 [''y''] 0 phi4"
value "execute_trivial_eval mytrace3 [''y''] 1 phi4"
value "execute_trivial_eval mytrace3 [''y''] 2 phi4"

end