(set-logic QF_SLIA)
(set-info :status unsat)
(declare-const x String)
(assert (str.in.re x (re.++ (str.to.re "abc") re.all)))
(assert (not (str.prefixof "abc" x)))
(check-sat)
