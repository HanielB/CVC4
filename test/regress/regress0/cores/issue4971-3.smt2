; COMMAND-LINE: --incremental -q --check-unsat-cores
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(declare-const v1 Bool)
(declare-const v2 Bool)
(declare-const v3 Bool)
(declare-const v5 Bool)
(declare-const v6 Bool)
(declare-const v9 Bool)
(declare-const v10 Bool)
(declare-const v11 Bool)
(declare-const v12 Bool)
(declare-const v13 Bool)
(declare-const i1 Int)
(declare-const i4 Int)
(declare-const r0 Real)
(declare-const r9 Real)
(declare-const r16 Real)
(declare-const Str3 String)
(declare-const Str5 String)
(declare-const Str6 String)
(declare-const Str9 String)
(declare-const Str10 String)
(declare-const Str11 String)
(declare-const Str19 String)
(assert (>= (str.len Str10) 45))
(assert (! (=> v11 v12) :named IP_1))
(assert (! (= (is_int 925.05885) (> i4 45) v13 v3 v6 v6) :named IP_2))
(check-sat)
(assert (! (=> v10 v9) :named IP_3))
(assert (str.in_re Str6(re.++ (str.to_re Str10) (str.to_re "wlzjqa" ))))
(assert (! (not v10) :named IP_4))
(check-sat-assuming (IP_2 IP_4))
(check-sat-assuming (IP_1 IP_3))
(assert (! (xor v3 v1 v5 v3 v2 (distinct Str19 Str3 Str5 Str9 Str11) (distinct 359 i1) v2 (>= r16 9873987263.0 r9 r0)) :named IP_6))
(check-sat)