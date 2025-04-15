(declare-const s String)

(assert (<= (str.len s) 10))
(assert (str.prefixof "hello" s))
(assert (str.prefixof "h" s))
(assert (str.suffixof "world" s))

(check-sat)
; the string assertions get combined into the following regex:
; (_*world&h_*&_{0,10}&hello_*)
; where e.g., "helloworld" is in the language
; if the max length was 9 the language would be empty instead
(get-model)
