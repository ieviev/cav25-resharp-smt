(declare-const regex RegLan)
(declare-const s String)

; does there exist a string of length 5 that contains 'a' 'b' and 'c'
(assert (= regex (re.parse "_{5}&_*a_*&_*b_*&_*c_*")))
(assert (str.in_re s regex))

(check-sat)
; get model prints that the trivially satisfiable node _{2} is reachable 
(get-model) 


(reset)
(declare-const regex RegLan)
(declare-const s String)
; does there exist a string of length 5 that contains ['a','b','c','d','e','f']
(assert (= regex (re.parse "_{5}&_*a_*&_*b_*&_*c_*&_*d_*&_*e_*&_*f_*")))
(assert (str.in_re s regex))
(check-sat)
; get model prints that the language is empty
(get-model) 