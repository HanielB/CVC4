; COMMAND-LINE: --finite-model-find
; EXPECT: unsat
(set-logic ALL_SUPPORTED)
(set-info :status unsat)
(declare-sort g_ 0)
(declare-fun __nun_card_witness_0_ () g_)
(declare-sort f_ 0)
(declare-fun __nun_card_witness_1_ () f_)
(declare-sort e_ 0)
(declare-fun __nun_card_witness_2_ () e_)
(declare-datatypes ((prod1_ 0))
 (((Pair1_ (_select_Pair1__0 e_) (_select_Pair1__1 f_)))))
(declare-sort d_ 0)
(declare-fun __nun_card_witness_3_ () d_)
(declare-sort c_ 0)
(declare-fun __nun_card_witness_4_ () c_)
(declare-sort b_ 0)
(declare-fun __nun_card_witness_5_ () b_)
(declare-sort a_ 0)
(declare-fun __nun_card_witness_6_ () a_)
(declare-datatypes ((prod_ 0))
 (((Pair_ (_select_Pair__0 a_) (_select_Pair__1 b_)))))
(declare-fun f1_ (prod_ c_ d_ prod1_) g_)
(declare-fun g1_ (prod_) c_)
(declare-fun h_ (prod_ d_) prod1_)
(declare-fun nun_sk_0_ () prod_)
(declare-fun nun_sk_1_ (c_) d_)
  (assert
   (not
    (exists ((v/72 c_))
     (exists ((x/73 prod1_))
      (= (f1_ nun_sk_0_ v/72 (nun_sk_1_ v/72) x/73)
       (f1_ nun_sk_0_ (g1_ nun_sk_0_) (nun_sk_1_ v/72)
        (h_ nun_sk_0_ (nun_sk_1_ v/72))))))))
(check-sat)
