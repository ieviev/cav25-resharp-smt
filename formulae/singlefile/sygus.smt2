
(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re (str.++ "C" "B")) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "A")))))) (let ((_let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "A" (str.++ "B" "C"))) (re.* re.allchar ) (str.to_re "A") (re.* re.allchar ))))) (and (not (= _let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) re.allchar  (re.* re.allchar ) _let_0 (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) _let_0 (re.* re.allchar ) re.allchar  (re.* re.allchar ))) _let_1))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" (str.++ "A" "B"))) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "A" "A")))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "A"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_1 _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "B"))) _let_0 (str.to_re "B") _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "A" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "B" (str.++ "A" "C"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "C" (str.++ "B" "B"))) (re.* re.allchar ) (str.to_re "A") (re.* re.allchar ))))) (and (not (= _let_0 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re "C") (re.* re.allchar ) (str.to_re (str.++ "B" (str.++ "B" "A"))) (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "B" (str.++ "B" (str.++ "C" "A")))) (re.* re.allchar ) re.allchar  (re.* re.allchar ))) _let_0)))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" "B"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re (str.++ "B" "B")) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.++ "C" "A"))) (let ((_let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re "A") (re.* re.allchar ) (str.to_re (str.++ "A" _let_0)) (re.* re.allchar ))))) (and (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "A" (str.++ "A" "C"))) (re.* re.allchar ) (str.to_re "A") (re.* re.allchar ))) _let_1)) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "A" "A")) (re.* re.allchar ) (str.to_re _let_0) (re.* re.allchar ))) _let_1))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.++ "A" _let_1))) (let ((_let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re _let_1) _let_0)))) (and (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))) (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "A" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "A")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_1) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (let ((_let_2 (str.++ "B" (str.++ "A" "C")))) (let ((_let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 _let_1 _let_0)))) (and (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re _let_2) _let_0)))) (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re (str.++ "B" (str.++ "A" "C"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (re.++ re.allchar  re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re "B") _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.to_re (str.++ "B" (str.++ "B" "A"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "B")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (re.++ re.allchar  re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re "A") _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re "C") (re.* re.allchar ) (str.to_re (str.++ "B" (str.++ "B" "A"))) (re.* re.allchar ))))) (and (not (= _let_0 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "C")))) (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "B" (str.++ "C" (str.++ "A" "C")))) (re.* re.allchar ) re.allchar  (re.* re.allchar ))) _let_0)))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "A"))) (let ((_let_2 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" _let_1))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "A" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re "C"))) (let ((_let_3 (str.to_re _let_1))) (let ((_let_4 (str.to_re (str.++ "C" _let_1)))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 _let_4 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_4 _let_0)))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "B" (str.++ "A" (str.++ "B" "A")))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 _let_1 _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "C" "C")))) (let ((_let_2 (str.++ "C" (str.++ "C" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "A" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "B" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "C" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "C" "B")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.++ "C" "C"))) (let ((_let_3 (str.to_re "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re (str.++ "C" (str.++ "C" "A"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.++ "C" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" "A"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "A" "C")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.to_re "B"))) (let ((_let_3 (str.++ "C" _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re _let_3) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_3)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re (str.++ "C" "B")) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "B" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "B")) _let_0 (str.to_re (str.++ "A" "B")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "B" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" _let_1))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.++ "A" _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "B")))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "C" "B")))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (let ((_let_2 (str.++ "A" (str.++ "C" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "A" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "B" (str.++ "A" "C"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "B" "B")))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 _let_2 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "C" "B")) (re.* re.allchar ) (str.to_re (str.++ "C" "B")) (re.* re.allchar ))))) (and (not (= _let_0 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re "C") (re.* re.allchar ) (str.to_re (str.++ "B" (str.++ "C" "B"))) (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "C" (str.++ "B" "C"))) (re.* re.allchar ) (str.to_re "B") (re.* re.allchar ))) _let_0)))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "B" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "C" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (let ((_let_2 (str.++ "A" (str.++ "A" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.++ "B" "A"))) (let ((_let_3 (str.to_re "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re _let_1) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.++ "C" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "C" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.++ "B" _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "B" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "C")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "B" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "A" "B")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "B" "C")))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "B" (str.++ "B" "B"))))) (let ((_let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "A")))) _let_0 re.allchar  _let_0)))) (and (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (re.++ re.allchar  re.allchar ) _let_0)))) (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re "A") _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "A" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "A"))) _let_0 (str.to_re "C") _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (let ((_let_2 (str.++ "C" "C"))) (let ((_let_3 (str.to_re (str.++ "B" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" _let_2))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "C" "C")))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 _let_2 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ re.allchar  _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.to_re "C"))) (let ((_let_3 (str.++ "B" (str.++ "B" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re _let_3) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_3)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "A" _let_1)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.++ "B" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "B" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "A" "A")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "B"))) _let_0 (str.to_re "C") _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" _let_1))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "C" (str.++ "A" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "A" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "B" "B")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re "B") (re.* re.allchar ) (str.to_re (str.++ "A" (str.++ "C" "B"))) (re.* re.allchar ))))) (and (not (= _let_0 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "C" (str.++ "C" (str.++ "B" "C")))) (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "B")))) (re.* re.allchar ) re.allchar  (re.* re.allchar ))) _let_0)))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "C")))) _let_0 re.allchar  _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "C" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "A" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "B" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "C" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "A" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_1 _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "C" "B")))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (let ((_let_2 (str.to_re (str.++ "C" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "A" "C")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "B" (str.++ "C" "C"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re (str.++ "C" "C")) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 _let_1 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re (str.++ "C" "B")) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "A")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" _let_1))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re (str.++ "C" "A")) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (let ((_let_2 (str.++ "B" _let_1))) (let ((_let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re _let_1) _let_0)))) (and (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))) (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "C"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re (str.++ "C" "C")) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (let ((_let_2 (str.to_re "C"))) (let ((_let_3 (str.to_re _let_1))) (let ((_let_4 (str.++ "B" (str.++ "A" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re _let_4) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_4)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "A" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re (str.++ "B" "C")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "C")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" "A"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re (str.++ "A" "A")) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "A" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ re.allchar  (str.to_re _let_1)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "A" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "A" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.to_re (str.++ "C" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "C" "B")) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "A" (str.++ "A" (str.++ "C" "A")))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "C" (str.++ "B" "C"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 _let_1 _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.++ "A" _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (let ((_let_2 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "C"))) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.++ "B" "C"))) (let ((_let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "C" "C")) (re.* re.allchar ) (str.to_re _let_0) (re.* re.allchar ))))) (and (not (= _let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "C" (str.++ "C" _let_0))) (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "C" (str.++ "C" "B"))) (re.* re.allchar ) (str.to_re "C") (re.* re.allchar ))) _let_1))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "B" "C")))) _let_0 re.allchar  _let_0)) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "B"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" (str.++ "B" "A"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re (str.++ "C" "C")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" _let_1))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" "C"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "A" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "C" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "C" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "C" "C")))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "B" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re _let_1) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "B" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "A"))) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "C" "A")))) (let ((_let_2 (str.++ "C" (str.++ "B" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "A" "A")))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ _let_2 re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "A" "B")))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re (str.++ "B" "C")) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" "B"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" (str.++ "B" "A"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "A" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "A" "C")))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (let ((_let_2 (str.++ "B" (str.++ "B" "C")))) (let ((_let_3 (str.to_re _let_2))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "B" (str.++ "A" "C"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "B" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re "A") _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re (str.++ "B" (str.++ "C" "A"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (re.++ re.allchar  re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re "A") _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "A" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" "A"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re (str.++ "A" "B")) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "C" "A"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (let ((_let_2 (str.to_re "A"))) (let ((_let_3 (str.to_re _let_1))) (let ((_let_4 (str.++ "C" (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_4)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re _let_4) _let_0)))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.++ "A" (str.++ "A" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re (str.++ "B" "A")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ (str.to_re (str.++ "A" _let_1)) re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "A"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re (str.++ "A" "B")) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (let ((_let_2 (str.to_re "A"))) (let ((_let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re _let_1) _let_0)))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "C"))) _let_0 _let_2 _let_0)) _let_3)) (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "A" _let_1)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "B" (str.++ "A" "C"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "A" "B")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.++ "C" "C"))) (let ((_let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "B" "C")) (re.* re.allchar ) (str.to_re _let_0) (re.* re.allchar ))))) (and (not (= _let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re "B") (re.* re.allchar ) (str.to_re (str.++ "C" _let_0)) (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "B" _let_0)) (re.* re.allchar ) (str.to_re "C") (re.* re.allchar ))) _let_1))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "A")))))) (let ((_let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "A" (str.++ "C" "B"))) (re.* re.allchar ) (str.to_re "A") (re.* re.allchar ))))) (and (not (= _let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) re.allchar  (re.* re.allchar ) _let_0 (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) _let_0 (re.* re.allchar ) re.allchar  (re.* re.allchar ))) _let_1))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "C" "A"))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (let ((_let_2 (str.++ "B" _let_1))) (let ((_let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "B")) _let_0 (str.to_re _let_1) _let_0)))) (and (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)))) (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (let ((_let_2 (str.++ "C" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "C" (str.++ "A" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "A" (str.++ "A" "B"))))) (let ((_let_2 (str.++ "B" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (re.++ re.allchar  re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re "A") _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ (str.to_re _let_2) re.allchar ) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.++ "A" "C"))) (let ((_let_3 (str.to_re _let_2))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_2)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "A"))) _let_0 (str.to_re "B") _let_0)))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" _let_1))) _let_0 re.allchar  _let_0)) _let_2)) (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "C" (str.++ "B" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "B" (str.++ "A" "C"))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.++ "C" _let_1))) (let ((_let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)))) (and (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))) (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re _let_2) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "C" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_1) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "A" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "C" "C")))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "A" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "B" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (let ((_let_2 (str.++ "B" (str.++ "A" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 _let_1 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "C" "B")))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.++ "A" "A"))) (let ((_let_1 (str.++ "C" _let_0))) (let ((_let_2 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re "B") (re.* re.allchar ) (str.to_re _let_1) (re.* re.allchar ))))) (and (not (= _let_2 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "B" _let_1)) (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "B" "C")) (re.* re.allchar ) (str.to_re _let_0) (re.* re.allchar ))) _let_2)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "C" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "A")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0 (str.to_re "C") _let_0)))) (and (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_1))) _let_0)))) (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re _let_1) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "C" "A"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (let ((_let_2 (str.to_re "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "B" (str.++ "A" "C"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" _let_1))) _let_0 re.allchar  _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (let ((_let_2 (str.++ "B" _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "A" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "C" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "A")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "C" (str.++ "B" "B"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "A")))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" "C"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 _let_1 _let_0)))) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 re.allchar  _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "B" (str.++ "A" (str.++ "B" "B")))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "B"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 _let_1 _let_0)))) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 re.allchar  _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "B")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "A" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re (str.++ "A" "B")) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re (str.++ "B" "B")) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "C" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "A")))) _let_0)))) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 re.allchar  _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "C" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "B" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "B" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "B" "C")))) (let ((_let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_1) _let_0)))) (and (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "C" "A")))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" _let_1))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "C")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.to_re "C"))) (let ((_let_3 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "B")) _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "B" _let_1)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "C" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.to_re "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re _let_1) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "C" "A")))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (let ((_let_2 (str.++ "B" (str.++ "A" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "B")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (let ((_let_2 (str.++ "A" (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 _let_1 _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.++ "C" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "B" "C")))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (let ((_let_2 (str.++ "A" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "C")) _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" _let_2))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.++ "A" _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" (str.++ "B" "C"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re "B"))) (let ((_let_3 (str.to_re "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re (str.++ "C" (str.++ "B" "B"))) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "B" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "B" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "A" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re (str.++ "B" "B")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "B" "C")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "A" (str.++ "C" "A"))))) (let ((_let_2 (str.++ "C" (str.++ "B" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ re.allchar  _let_1) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (let ((_let_2 (str.++ "A" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" _let_2))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "A" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" _let_1))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.++ "B" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_2))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "C")) _let_0 (str.to_re _let_1) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" (str.++ "B" "A"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_1))) _let_0 re.allchar  _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (let ((_let_2 (str.++ "B" _let_1))) (let ((_let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re _let_1) _let_0)))) (and (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)))) (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.++ "A" _let_1))) (let ((_let_3 (str.++ "C" _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_3) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_3)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" _let_1))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "B")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" (str.++ "C" "B"))) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.to_re "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" "B"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re (str.++ "C" "A")) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "A" "B")))))) (let ((_let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "B" (str.++ "C" "A"))) (re.* re.allchar ) (str.to_re "B") (re.* re.allchar ))))) (and (not (= _let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) re.allchar  (re.* re.allchar ) _let_0 (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) _let_0 (re.* re.allchar ) re.allchar  (re.* re.allchar ))) _let_1))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "C" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "A" "C")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "A" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re (str.++ "A" "B")) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re _let_1) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "B")))) _let_0 re.allchar  _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.++ "C" _let_1))) (let ((_let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)))) (and (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))) (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re _let_2) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "A" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "A"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_1 _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "B" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "A" "A")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "C" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "C" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "B" "C")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (let ((_let_2 (str.++ "A" (str.++ "C" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "A" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_1) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" _let_1))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "A" "C")))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "C" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "A" "A")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "A" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "A")))) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (let ((_let_2 (str.++ "A" _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" _let_1))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "B")))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "C" (str.++ "A" "B"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (let ((_let_2 (str.++ "A" (str.++ "A" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "B" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "A" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (let ((_let_2 (str.++ "A" (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re (str.++ "A" "A")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 _let_1 _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "C" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "B" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" _let_1))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "A" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (let ((_let_2 (str.to_re (str.++ "A" (str.++ "A" "A"))))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_2 _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (let ((_let_2 (str.++ "C" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.++ "B" _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "C" "C")))) _let_0 re.allchar  _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (let ((_let_2 (str.++ "B" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" _let_2))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re (str.++ "B" "A")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (let ((_let_2 (str.to_re (str.++ "C" (str.++ "C" "C"))))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_2 _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" _let_1))) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re _let_1))) (let ((_let_3 (str.to_re (str.++ "C" _let_1)))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 _let_3 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 _let_3 _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "C" (str.++ "A" "B"))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "B" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "B" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (let ((_let_2 (str.to_re "A"))) (let ((_let_3 (str.to_re (str.++ "A" (str.++ "A" "A"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_3 _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (let ((_let_2 (str.to_re (str.++ "B" (str.++ "A" "B"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "C" (str.++ "B" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (re.++ re.allchar  re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_1 _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" _let_1))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.++ "C" _let_1))) (let ((_let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)))) (and (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re _let_2) _let_0)))) (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "B" "A")))) (let ((_let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "B"))) _let_0 (str.to_re "A") _let_0)))) (and (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_1) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.++ "B" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "B" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" _let_2))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" "C"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" "C"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "A" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "A" "A")))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "C" (str.++ "C" "A"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "A" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "A"))) _let_0 (str.to_re "A") _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.++ "A" "C"))) (let ((_let_3 (str.to_re _let_2))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ (str.to_re (str.++ "C" _let_1)) re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" _let_1))) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" _let_1))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "B")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re (str.++ "C" "B")) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "A"))) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re (str.++ "A" "B")) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re (str.++ "C" "A")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "C" (str.++ "B" "B"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" "C"))) _let_0 (str.to_re "A") _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "C" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.++ "C" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "B" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 (re.++ re.allchar  re.allchar ) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (let ((_let_2 (str.++ "B" _let_1))) (let ((_let_3 (str.to_re _let_2))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_1))) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "C" "A"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "C" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "B")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re (str.++ "B" "C")))) (let ((_let_3 (str.to_re (str.++ "B" _let_1)))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re _let_1) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "C" "A")) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "C" (str.++ "C" "C"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ re.allchar  _let_1) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "C" "B")) (re.* re.allchar ) (str.to_re (str.++ "C" "B")) (re.* re.allchar ))))) (and (not (= _let_0 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "C" (str.++ "B" (str.++ "C" "B")))) (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "C" (str.++ "B" "C"))) (re.* re.allchar ) (str.to_re "B") (re.* re.allchar ))) _let_0)))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "C" "B")))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 _let_2 _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (let ((_let_2 (str.++ "B" (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "A")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "C" "C")))) _let_0 re.allchar  _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "A" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "B" (str.++ "A" (str.++ "A" "C")))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" (str.++ "A" "C"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 _let_1 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0 (str.to_re "C") _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "C" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" _let_1))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (let ((_let_2 (str.++ "B" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "B" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" _let_2))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "A" "B")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.to_re "C"))) (let ((_let_1 (str.to_re (str.++ "C" (str.++ "C" "C"))))) (let ((_let_2 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "C" "C")) (re.* re.allchar ) (str.to_re (str.++ "C" "C")) (re.* re.allchar ))))) (and (not (= _let_2 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) _let_0 (re.* re.allchar ) _let_1 (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) _let_1 (re.* re.allchar ) _let_0 (re.* re.allchar ))) _let_2)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "C" "C")))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 _let_2 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ re.allchar  _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "C" (str.++ "B" "C"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "C" "C")))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" "C"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_1 _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "B" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ (str.to_re _let_1) re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.++ "B" _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "B" "C")))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (let ((_let_2 (str.++ "A" (str.++ "C" "A")))) (let ((_let_3 (str.to_re _let_2))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ re.allchar  _let_3) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "C"))) _let_0 _let_1 _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "C" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" (str.++ "C" "B"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.++ "B" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" _let_2))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "C" (str.++ "B" "C"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "A" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ _let_1 re.allchar ) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.to_re (str.++ "A" (str.++ "C" "A"))))) (let ((_let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) re.allchar  (re.* re.allchar ) (re.++ re.allchar  _let_0) (re.* re.allchar ))))) (and (not (= _let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "A" (str.++ "A" (str.++ "C" "A")))) (re.* re.allchar ))))) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re "A") (re.* re.allchar ) _let_0 (re.* re.allchar ))) _let_1))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" "C"))) _let_0 (str.to_re "B") _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.++ "A" (str.++ "C" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.++ "B" "A"))) (let ((_let_3 (str.++ "B" _let_2))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_3)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ (str.to_re _let_3) re.allchar ) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" _let_1))) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.++ "C" _let_1))) (let ((_let_3 (str.to_re _let_2))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ re.allchar  _let_3) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 _let_3 _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (str.++ "C" "C"))) (let ((_let_1 (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re "B") (re.* re.allchar ) (str.to_re (str.++ "C" _let_0)) (re.* re.allchar ))))) (and (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "B" _let_0)) (re.* re.allchar ) (str.to_re "C") (re.* re.allchar ))) _let_1)) (not (= (str.in_re x (re.++ (re.* re.allchar ) re.allchar  (re.* re.allchar ) (str.to_re (str.++ "B" "C")) (re.* re.allchar ) (str.to_re _let_0) (re.* re.allchar ))) _let_1))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.++ "A" _let_1))) (let ((_let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re _let_1) _let_0)))) (and (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)))) (not (= _let_3 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) _let_2)) (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "C" "B")))) (let ((_let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" "C"))) _let_0 (str.to_re "B") _let_0)))) (and (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_1) _let_0)))) (not (= _let_2 (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "C"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re (str.++ "C" "C")) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (let ((_let_2 (str.to_re _let_1))) (let ((_let_3 (str.to_re (str.++ "C" (str.++ "A" (str.++ "C" "C")))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 _let_3 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "A" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "B")))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "A" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "C" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "A" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "A" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "B" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "B")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0 (str.to_re "A") _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "B")))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "A" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re _let_1))) (let ((_let_3 (str.to_re (str.++ "C" _let_1)))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 _let_3 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 _let_3 _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.++ "A" (str.++ "A" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ (str.to_re (str.++ "A" _let_1)) re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re (str.++ "B" "A")) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (let ((_let_2 (str.++ "C" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re (str.++ "B" "A")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "B")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.to_re "A"))) (let ((_let_3 (str.to_re _let_1))) (let ((_let_4 (str.to_re (str.++ "A" "B")))) (and (not (= (str.in_re x (re.++ _let_0 _let_4 _let_0 _let_3 _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 _let_2 _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 re.allchar  _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" "A"))) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_4 _let_0 _let_3 _let_0)))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re "C"))) (let ((_let_3 (str.++ "C" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_3)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re _let_3) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "A" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" "B"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" (str.++ "B" "A"))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.++ "B" "C"))) (let ((_let_3 (str.to_re (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_2))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (let ((_let_2 (str.++ "A" (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" "A"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re (str.++ "A" "A")) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "B" "A")))) (and (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ (str.to_re _let_1) re.allchar ) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (let ((_let_2 (str.to_re _let_1))) (let ((_let_3 (str.to_re (str.++ "C" (str.++ "A" (str.++ "C" "C")))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 _let_3 _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" "A"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "A" "C")) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re "B"))) (let ((_let_3 (str.to_re (str.++ "B" _let_1)))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "A") _let_0 _let_3 _let_0 re.allchar  _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "C" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "A" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "B" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "B")))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "A" (str.++ "A" (str.++ "C" "A")))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "A" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 _let_1 _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" "A"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "A" "B")) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "A"))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "A" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.++ "A" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "C" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_2))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (let ((_let_2 (str.++ "B" (str.++ "B" "C")))) (let ((_let_3 (str.to_re _let_2))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ (str.to_re _let_1) re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "B" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "B"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_1 _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "C" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" _let_1))) _let_0 re.allchar  _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "B" "B")))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "B")) _let_0 (str.to_re (str.++ "B" "B")) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 _let_2 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ _let_2 re.allchar ) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" _let_1))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "C" "A")))) (let ((_let_2 (str.to_re (str.++ "A" _let_1)))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 _let_2 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (let ((_let_2 (str.to_re "B"))) (let ((_let_3 (str.to_re (str.++ "A" (str.++ "B" "C"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 _let_1 _let_0 re.allchar  _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_3 _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "A" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_1) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "C" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "A")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.++ "B" "A"))) (let ((_let_3 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "B")) _let_0 (str.to_re (str.++ "A" "B")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 _let_3 _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.++ "B" "C"))) (let ((_let_3 (str.to_re "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" _let_2))) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "C" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "C")))) _let_0 re.allchar  _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "A" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "C" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "B" "C")))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.to_re (str.++ "A" (str.++ "A" "A"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 (str.to_re "A") _let_0 _let_2 _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (re.++ re.allchar  re.allchar ) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "A" (str.++ "A" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "C" "B")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "B")))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "C" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 _let_1 _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "A"))) (let ((_let_2 (str.++ "A" (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re (str.++ "A" "A")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (let ((_let_2 (str.to_re (str.++ "A" (str.++ "B" "B"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re (str.++ "B" "B")) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_2 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" (str.++ "B" "C"))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.++ "B" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" _let_1))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "C")) _let_0 (str.to_re _let_1) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ (str.to_re _let_2) re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "B")) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "B" "B")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ (str.to_re _let_1) re.allchar ) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.++ "C" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" _let_2))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 (re.++ re.allchar  re.allchar ) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 (str.to_re "A") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re _let_2) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "A" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "A" "B")))) _let_0 re.allchar  _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "A" "C")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "B")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.to_re "A"))) (let ((_let_3 (str.++ "A" _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_3)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_3) _let_0 _let_2 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" "A"))) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" "B"))) _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "A")) _let_0 (str.to_re (str.++ "B" "C")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "C" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "A"))) (let ((_let_2 (str.++ "C" "A"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" _let_2))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re _let_2) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "A" "C")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "C")) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "C" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "B" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "B")))) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (let ((_let_2 (str.to_re (str.++ "A" (str.++ "A" "B"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" "A"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 _let_2 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "B" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re "A") _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "B" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "A" (str.++ "C" "C")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_1) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "C" (str.++ "B" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "A" "B")))) _let_0 re.allchar  _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "A")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (let ((_let_2 (str.++ "A" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_1) _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "B" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" _let_1))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "A"))) (let ((_let_2 (str.to_re "A"))) (let ((_let_3 (str.to_re _let_1))) (let ((_let_4 (str.to_re (str.++ "A" (str.++ "A" "A"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 _let_3 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_4 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_4 _let_0)))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" "C")) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "B" "B")))) _let_0))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "B"))) (let ((_let_2 (str.++ "A" "B"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" _let_1))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "A" (str.++ "B" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_2)) _let_0 (str.to_re "C") _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "B" "A")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "C")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "B" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "B" (str.++ "A" "B")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" "C"))) _let_0 (str.to_re "B") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" (str.++ "C" "B"))) _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re (str.++ "A" (str.++ "C" (str.++ "C" "C")))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.inter re.allchar  (str.to_re "")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" (str.++ "C" (str.++ "A" "B")))) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 _let_1 _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (let ((_let_2 (str.++ "A" "C"))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" (str.++ "B" (str.++ "C" "A")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" _let_2))) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" "C"))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (let ((_let_2 (str.to_re (str.++ "B" "C")))) (let ((_let_3 (str.++ "B" (str.++ "B" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re _let_3) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_3)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "B"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "B" "A")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "B") _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (not (= (str.in_re x (re.++ _let_0 (str.to_re (str.++ "A" "B")) _let_0 (str.to_re _let_1) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0 re.allchar  _let_0)))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "C" "C"))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" "B")) _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re (str.++ "C" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "A" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0 re.allchar  _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "B" (str.++ "A" "A")))) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "B" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "B" (str.++ "B" "B")))) (let ((_let_2 (str.to_re _let_1))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" "B")) _let_0 (str.to_re (str.++ "B" "B")) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 _let_2 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (re.++ _let_2 re.allchar ) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" _let_1)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.++ "C" "A"))) (let ((_let_3 (str.to_re "A"))) (let ((_let_4 (str.to_re (str.++ "A" "A")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_4 _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_4 _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" "B"))) (let ((_let_2 (str.to_re (str.++ "A" "A")))) (let ((_let_3 (str.to_re (str.++ "A" _let_1)))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 (str.to_re "C") _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re (str.++ "B" "C")) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 _let_3 _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.++ "A" (str.++ "C" "A")))) (let ((_let_2 (str.++ "C" (str.++ "B" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "A") _let_0 (str.to_re _let_1) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_1)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "C") _let_0 (str.to_re _let_2) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "C" _let_2)) _let_0)))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "C"))) (let ((_let_2 (str.to_re (str.++ "C" "C")))) (let ((_let_3 (str.to_re (str.++ "C" (str.++ "C" "C"))))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" "C"))) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re "B") _let_0 _let_3 _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_3 _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_2 _let_0 _let_2 _let_0))))))))))
(check-sat)


(reset)

(set-logic QF_S)




(declare-fun x () String)
(assert (let ((_let_0 (re.* re.allchar ))) (let ((_let_1 (str.to_re "B"))) (let ((_let_2 (str.++ "B" (str.++ "A" "C")))) (and (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "B" (str.++ "C" (str.++ "B" "B")))) _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 re.allchar  _let_0 (str.to_re (str.++ "A" _let_2)) _let_0)))) (not (= (str.in_re x (re.++ _let_0 re.allchar  _let_0 (str.to_re _let_2) _let_0 _let_1 _let_0)) (str.in_re x (re.++ _let_0 re.allchar  _let_0 _let_1 _let_0 (str.to_re (str.++ "A" (str.++ "C" "B"))) _let_0)))))))))
(check-sat)

