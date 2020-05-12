(declare-fun a () Bool)

(assert (and a (not a)))

(check-sat)

(exit)
