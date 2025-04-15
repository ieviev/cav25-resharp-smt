(set-logic QF_S)
(declare-const re1 RegLan)
(declare-const re2 RegLan)
(declare-const re3 RegLan)
(declare-const s String)

(assert (= re1 (re.parse "(_*a_*){5}")))
(assert (= re2 (re.parse "(_*b_*){5}")))
;(assert (= re3 (re.parse "_*[0-9]")))

(assert (str.in_re s (re.inter re1 re2)))
;(assert (<= 10 (str.len s)))

(check-sat)
;(get-model)