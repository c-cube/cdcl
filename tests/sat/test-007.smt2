(declare-sort $i 0)
(declare-fun a () $i)
(declare-fun b () $i)
(declare-fun c () $i)
(assert (and (= a b) (= b c)))
(check-sat)
