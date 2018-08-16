; COMMAND-LINE: --ext-rew-prep --ext-rew-prep-agg
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic QF_NIA)
(set-info :source |
Generated by: Cristina Borralleras, Daniel Larraz, Albert Oliveras, Enric Rodriguez-Carbonell, Albert Rubio
Generated on: 2017-04-27
Generator: VeryMax
Application: Termination proving
Target solver: barcelogic
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status sat)
(declare-fun global_invc1_0 () Int)
(declare-fun lam0n0 () Int)
(declare-fun lam0n2 () Int)
(declare-fun global_invc1_1 () Int)
(declare-fun lam0n1 () Int)
(declare-fun lam1n0 () Int)
(declare-fun lam1n1 () Int)
(declare-fun lam1n3 () Int)
(declare-fun lam1n4 () Int)
(declare-fun lam1n2 () Int)
(declare-fun term_invc1_0 () Int)
(declare-fun lam2n0 () Int)
(declare-fun lam2n1 () Int)
(declare-fun lam2n3 () Int)
(declare-fun lam2n4 () Int)
(declare-fun lam2n5 () Int)
(declare-fun lam2n6 () Int)
(declare-fun lam2n7 () Int)
(declare-fun lam2n8 () Int)
(declare-fun lam2n9 () Int)
(declare-fun lam2n10 () Int)
(declare-fun lam2n11 () Int)
(declare-fun lam2n12 () Int)
(declare-fun lam2n13 () Int)
(declare-fun lam2n2 () Int)
(declare-fun term_invc1_1 () Int)
(declare-fun non_inc1_L () Bool)
(declare-fun lam3n0 () Int)
(declare-fun lam3n1 () Int)
(declare-fun lam3n3 () Int)
(declare-fun lam3n4 () Int)
(declare-fun lam3n5 () Int)
(declare-fun lam3n6 () Int)
(declare-fun lam3n7 () Int)
(declare-fun lam3n8 () Int)
(declare-fun lam3n9 () Int)
(declare-fun lam3n10 () Int)
(declare-fun lam3n11 () Int)
(declare-fun lam3n12 () Int)
(declare-fun lam3n13 () Int)
(declare-fun lam3n15 () Int)
(declare-fun lam3n14 () Int)
(declare-fun lam3n2 () Int)
(declare-fun rfc0 () Int)
(declare-fun disabled1_L () Bool)
(declare-fun bounded1_L () Bool)
(declare-fun lam4n0 () Int)
(declare-fun lam4n1 () Int)
(declare-fun lam4n3 () Int)
(declare-fun lam4n4 () Int)
(declare-fun lam4n5 () Int)
(declare-fun lam4n6 () Int)
(declare-fun lam4n7 () Int)
(declare-fun lam4n8 () Int)
(declare-fun lam4n9 () Int)
(declare-fun lam4n10 () Int)
(declare-fun lam4n11 () Int)
(declare-fun lam4n12 () Int)
(declare-fun lam4n13 () Int)
(declare-fun lam4n14 () Int)
(declare-fun lam4n2 () Int)
(declare-fun rfc1 () Int)
(declare-fun dec1_L () Bool)
(declare-fun lam5n0 () Int)
(declare-fun lam5n1 () Int)
(declare-fun lam5n3 () Int)
(declare-fun lam5n4 () Int)
(declare-fun lam5n5 () Int)
(declare-fun lam5n6 () Int)
(declare-fun lam5n7 () Int)
(declare-fun lam5n8 () Int)
(declare-fun lam5n9 () Int)
(declare-fun lam5n10 () Int)
(declare-fun lam5n11 () Int)
(declare-fun lam5n12 () Int)
(declare-fun lam5n13 () Int)
(declare-fun lam5n14 () Int)
(declare-fun lam5n2 () Int)
(declare-fun bnd_and_dec1_L () Bool)
(declare-fun GLOBAL_NT_1 () Bool)
(declare-fun global_V0_1 () Int)
(declare-fun TERM_NT_1 () Bool)
(declare-fun term_V0_1 () Int)
(declare-fun ALL_NON_INC_0 () Bool)
(declare-fun DIS_OR_ALL_NON_INC_0 () Bool)
(declare-fun SOME_BND_AND_DEC_0 () Bool)
(declare-fun V0_NIV () Int)
(declare-fun V1_NIV () Int)
(assert ( and ( >= global_invc1_0 ( - 1 ) ) ( <= global_invc1_0 1 ) ( and ( >= lam0n0 0 ) ( <= 0 lam0n2 ) ( < lam0n2 1 ) ( and ( = ( * ( - 1 ) lam0n0 ) ( + global_invc1_1 ( * ( - 1 ) lam0n2 ) ) ) ( = ( * lam0n1 1 ) 0 ) ( = ( * lam0n1 ( - 1 ) ) global_invc1_0 ) ) ) ( and ( >= lam1n0 0 ) ( >= lam1n1 0 ) ( >= lam1n3 0 ) ( <= 0 lam1n4 ) ( < lam1n4 1 ) ( and ( = ( + ( * ( - 1 ) lam1n0 ) ( * lam1n1 ( - 999 ) ) ( * lam1n2 1000 ) ( * lam1n3 global_invc1_1 ) ) ( + global_invc1_1 ( * ( - 1 ) lam1n4 ) ) ) ( = ( + ( * lam1n1 ( - 1 ) ) ( * lam1n2 1 ) ( * lam1n3 global_invc1_0 ) ) 0 ) ( = ( * lam1n2 ( - 1 ) ) global_invc1_0 ) ) ) ( >= term_invc1_0 ( - 1 ) ) ( <= term_invc1_0 1 ) ( and ( >= lam2n0 0 ) ( >= lam2n1 0 ) ( >= lam2n3 0 ) ( >= lam2n4 0 ) ( >= lam2n5 0 ) ( >= lam2n6 0 ) ( >= lam2n7 0 ) ( >= lam2n8 0 ) ( >= lam2n9 0 ) ( >= lam2n10 0 ) ( >= lam2n11 0 ) ( >= lam2n12 0 ) ( <= 0 lam2n13 ) ( < lam2n13 1 ) ( and ( = ( + ( * ( - 1 ) lam2n0 ) ( * lam2n1 ( - 999 ) ) ( * lam2n2 1000 ) ( * lam2n3 50001 ) ( * lam2n4 ( - 1 ) ) ( * lam2n5 1 ) ( * lam2n6 2 ) ( * lam2n7 3 ) ( * lam2n8 55 ) ( * lam2n9 58 ) ( * lam2n10 61 ) ( * lam2n11 62 ) ( * lam2n12 global_invc1_1 ) ) ( + term_invc1_1 ( * ( - 1 ) lam2n13 ) ) ) ( = ( + ( * lam2n1 ( - 1 ) ) ( * lam2n2 1 ) ( * lam2n3 ( - 1 ) ) ( * lam2n4 ( - 1 ) ) ( * lam2n5 ( - 1 ) ) ( * lam2n6 ( - 1 ) ) ( * lam2n7 ( - 1 ) ) ( * lam2n8 ( - 1 ) ) ( * lam2n9 ( - 1 ) ) ( * lam2n10 ( - 1 ) ) ( * lam2n11 ( - 1 ) ) ( * lam2n12 global_invc1_0 ) ) 0 ) ( = ( * lam2n2 ( - 1 ) ) term_invc1_0 ) ) ) ( = non_inc1_L ( and ( >= lam3n0 0 ) ( >= lam3n1 0 ) ( >= lam3n3 0 ) ( >= lam3n4 0 ) ( >= lam3n5 0 ) ( >= lam3n6 0 ) ( >= lam3n7 0 ) ( >= lam3n8 0 ) ( >= lam3n9 0 ) ( >= lam3n10 0 ) ( >= lam3n11 0 ) ( >= lam3n12 0 ) ( >= lam3n13 0 ) ( <= 0 lam3n15 ) ( < lam3n15 1 ) ( <= lam3n14 1 ) ( >= lam3n14 0 ) ( and ( > ( + ( * ( - 1 ) lam3n0 ) ( * lam3n1 ( - 999 ) ) ( * lam3n2 1000 ) ( * lam3n3 50001 ) ( * lam3n4 ( - 1 ) ) ( * lam3n5 1 ) ( * lam3n6 2 ) ( * lam3n7 3 ) ( * lam3n8 55 ) ( * lam3n9 58 ) ( * lam3n10 61 ) ( * lam3n11 62 ) ( * lam3n12 global_invc1_1 ) ( * lam3n13 term_invc1_1 ) ( * lam3n14 ( + 1 ( * ( - 1 ) lam3n15 ) ) ) ) 0 ) ( = ( + ( * lam3n1 ( - 1 ) ) ( * lam3n2 1 ) ( * lam3n3 ( - 1 ) ) ( * lam3n4 ( - 1 ) ) ( * lam3n5 ( - 1 ) ) ( * lam3n6 ( - 1 ) ) ( * lam3n7 ( - 1 ) ) ( * lam3n8 ( - 1 ) ) ( * lam3n9 ( - 1 ) ) ( * lam3n10 ( - 1 ) ) ( * lam3n11 ( - 1 ) ) ( * lam3n12 global_invc1_0 ) ( * lam3n13 term_invc1_0 ) ( * lam3n14 rfc0 ) ) 0 ) ( = ( + ( * lam3n2 ( - 1 ) ) ( * lam3n14 ( * ( - 1 ) rfc0 ) ) ) 0 ) ) ) ) ( = disabled1_L ( and ( = lam3n14 0 ) non_inc1_L ) ) ( = bounded1_L ( and ( >= lam4n0 0 ) ( >= lam4n1 0 ) ( >= lam4n3 0 ) ( >= lam4n4 0 ) ( >= lam4n5 0 ) ( >= lam4n6 0 ) ( >= lam4n7 0 ) ( >= lam4n8 0 ) ( >= lam4n9 0 ) ( >= lam4n10 0 ) ( >= lam4n11 0 ) ( >= lam4n12 0 ) ( >= lam4n13 0 ) ( <= 0 lam4n14 ) ( < lam4n14 1 ) ( and ( = ( + ( * ( - 1 ) lam4n0 ) ( * lam4n1 ( - 999 ) ) ( * lam4n2 1000 ) ( * lam4n3 50001 ) ( * lam4n4 ( - 1 ) ) ( * lam4n5 1 ) ( * lam4n6 2 ) ( * lam4n7 3 ) ( * lam4n8 55 ) ( * lam4n9 58 ) ( * lam4n10 61 ) ( * lam4n11 62 ) ( * lam4n12 global_invc1_1 ) ( * lam4n13 term_invc1_1 ) ) ( + ( * ( - 1 ) rfc1 ) ( * ( - 1 ) lam4n14 ) ) ) ( = ( + ( * lam4n1 ( - 1 ) ) ( * lam4n2 1 ) ( * lam4n3 ( - 1 ) ) ( * lam4n4 ( - 1 ) ) ( * lam4n5 ( - 1 ) ) ( * lam4n6 ( - 1 ) ) ( * lam4n7 ( - 1 ) ) ( * lam4n8 ( - 1 ) ) ( * lam4n9 ( - 1 ) ) ( * lam4n10 ( - 1 ) ) ( * lam4n11 ( - 1 ) ) ( * lam4n12 global_invc1_0 ) ( * lam4n13 term_invc1_0 ) ) ( * ( - 1 ) rfc0 ) ) ( = ( * lam4n2 ( - 1 ) ) 0 ) ) ) ) ( = dec1_L ( and ( >= lam5n0 0 ) ( >= lam5n1 0 ) ( >= lam5n3 0 ) ( >= lam5n4 0 ) ( >= lam5n5 0 ) ( >= lam5n6 0 ) ( >= lam5n7 0 ) ( >= lam5n8 0 ) ( >= lam5n9 0 ) ( >= lam5n10 0 ) ( >= lam5n11 0 ) ( >= lam5n12 0 ) ( >= lam5n13 0 ) ( <= 0 lam5n14 ) ( < lam5n14 1 ) ( and ( = ( + ( * ( - 1 ) lam5n0 ) ( * lam5n1 ( - 999 ) ) ( * lam5n2 1000 ) ( * lam5n3 50001 ) ( * lam5n4 ( - 1 ) ) ( * lam5n5 1 ) ( * lam5n6 2 ) ( * lam5n7 3 ) ( * lam5n8 55 ) ( * lam5n9 58 ) ( * lam5n10 61 ) ( * lam5n11 62 ) ( * lam5n12 global_invc1_1 ) ( * lam5n13 term_invc1_1 ) ) ( + 1 ( * ( - 1 ) lam5n14 ) ) ) ( = ( + ( * lam5n1 ( - 1 ) ) ( * lam5n2 1 ) ( * lam5n3 ( - 1 ) ) ( * lam5n4 ( - 1 ) ) ( * lam5n5 ( - 1 ) ) ( * lam5n6 ( - 1 ) ) ( * lam5n7 ( - 1 ) ) ( * lam5n8 ( - 1 ) ) ( * lam5n9 ( - 1 ) ) ( * lam5n10 ( - 1 ) ) ( * lam5n11 ( - 1 ) ) ( * lam5n12 global_invc1_0 ) ( * lam5n13 term_invc1_0 ) ) ( * ( - 1 ) rfc0 ) ) ( = ( * lam5n2 ( - 1 ) ) rfc0 ) ) ) ) ( = bnd_and_dec1_L ( and bounded1_L dec1_L ) ) ( = GLOBAL_NT_1 ( not ( = global_invc1_0 0 ) ) ) ( or ( not ( <= ( + global_invc1_1 ( * global_invc1_0 global_V0_1 ) ) 0 ) ) ( = global_invc1_0 0 ) ) ( = TERM_NT_1 ( not ( = term_invc1_0 0 ) ) ) ( or ( and ( not ( <= ( + term_invc1_1 ( * term_invc1_0 term_V0_1 ) ) 0 ) ) ( <= ( + ( * ( - 1 ) term_V0_1 ) ( - 1 ) ) 0 ) ( <= ( + ( * ( - 1 ) term_V0_1 ) 1 ) 0 ) ( <= ( + ( * ( - 1 ) term_V0_1 ) 2 ) 0 ) ( <= ( + ( * ( - 1 ) term_V0_1 ) 3 ) 0 ) ( <= ( + ( * ( - 1 ) term_V0_1 ) 55 ) 0 ) ( <= ( + ( * ( - 1 ) term_V0_1 ) 58 ) 0 ) ( <= ( + ( * ( - 1 ) term_V0_1 ) 61 ) 0 ) ( <= ( + ( * ( - 1 ) term_V0_1 ) 62 ) 0 ) ) ( = term_invc1_0 0 ) ) ( = ALL_NON_INC_0 non_inc1_L ) ( = DIS_OR_ALL_NON_INC_0 ( or disabled1_L ALL_NON_INC_0 ) ) ( = SOME_BND_AND_DEC_0 bnd_and_dec1_L ) ( or ( not ALL_NON_INC_0 ) ( and ( >= rfc0 ( - 2 ) ) ( <= rfc0 2 ) ( not ( = rfc0 0 ) ) ( >= rfc1 0 ) ( or SOME_BND_AND_DEC_0 ( or ( and ( <= ( + ( * rfc0 V0_NIV ) 1 ) ( * rfc0 V1_NIV ) ) ( >= ( * ( - 1 ) V0_NIV ) ( * ( - 1 ) V1_NIV ) ) ) ( = rfc0 0 ) ) ) ) ) ( or GLOBAL_NT_1 TERM_NT_1 ALL_NON_INC_0 ) ))
(check-sat)
(exit)
