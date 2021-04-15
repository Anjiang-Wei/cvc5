; COMMAND-LINE: --cegqi
; EXPECT: unsat
(set-logic UFNIRA)
(set-info :status unsat)
(declare-const y Int)
(assert (and (= y 1) (forall ((X Int)) (= X 12) )))
(check-sat)
