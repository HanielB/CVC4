(set-logic QF_UF)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun f1 () U)
(declare-fun f2 () U)
(declare-fun f3 () U)
(declare-fun f4 () U)
(declare-fun p (U) Bool)
(assert (= f1 f2))
(assert (=> (p f1) (or (= f1 f2) (distinct f3 f4 f2)) (p f3)))
(assert (p f1))
(assert (not (p f3)))
(check-sat)
(exit)


