; EXPECT: sat
(set-logic ALL)
(set-option :check-proofs true)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (not (ite a b c)))
(assert b)
(assert (not c))
(check-sat)