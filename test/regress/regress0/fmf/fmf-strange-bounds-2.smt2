; COMMAND-LINE: --finite-model-find --fmf-bound --no-check-unsat-cores-new
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-sort U 0)
(declare-fun P (Int U) Bool)

(declare-fun S (U) (Set Int))

(declare-fun f (U) U)

(assert (forall ((x Int) (z U))
(=> (member x (S (f z)))
(P x z))))

; need model of U size 2 to satisfy these
(declare-fun a () U)
(assert (member 77 (S a)))
(assert (not (P 77 a)))

; unsat
(assert (forall ((x U) (y U)) (= x y)))

(check-sat)
