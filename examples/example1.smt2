(declare-const re1 RegLan)
(declare-const re2 RegLan)
(declare-const s String)

; (a|b) subsumes (a)

(assert (= re1 (re.parse "a|b")))
(assert (= re2 (re.parse "a")))

; encoded as "does there exist a member in (a) that is not in (a|b)"

(assert (str.in_re s re2))
(assert (not (str.in_re s re1)))

(check-sat)
