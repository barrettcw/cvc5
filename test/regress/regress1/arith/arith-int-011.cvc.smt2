; EXPECT: sat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert (= (+ (+ (+ (* 13 x0) (* (- 1) x1)) (* 11 x2)) (* 10 x3)) 9))
(assert (>= (+ (+ (+ (* (- 7) x0) (* 3 x1)) (* (- 22) x2)) (* 16 x3)) 9))
(check-sat-assuming ( (not false) ))