; COMMAND-LINE: --arith-idl-ext
(set-option :produce-models true)
(set-logic QF_IDL)
(set-info :source |Tests out a variety of syntaxes that the rewriter should support
Matthew Sotoudeh
|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (or (and (= 5 x) (= 6 x))
            (and (= 10 y) (= 8 y))
            (and (= (- 1) z) (= (- 1) z))))
(check-sat)
(get-model)
