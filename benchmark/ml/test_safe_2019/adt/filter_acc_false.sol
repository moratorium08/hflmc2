sat
(model
  (define-fun |length[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (or (= (+ v_0 (* (- 1) v_1)) 0) (and (= v_1 0) (>= (* (- 1) v_0) 0) (not (= (+ v_0 (* (- 1) v_1)) 0))))
  )
  (define-fun |make_intlist[0:1][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun |make_intlist[0:1][0:1][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) Bool
    true
  )
  (define-fun |filter_acc[0:3]|
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun |filter_acc[0:5][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    (= (+ v_2 (* (- 1) v_0)) 0)
  )
  (define-fun |length[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |fail_102[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |make_intlist[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |filter_acc[0:0][0:1][0:0]|
    ( (v_0 Int) (v_1 Bool) ) Bool
    (exists ( (v_2 Int) (v_3 Int) ) (and (not v_1) (|make_intlist[0:1][0:0]| v_2 v_3)))
  )
  (define-fun |filter_acc[0:4][0:1][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Int) ) Bool
    (exists ( (v_4 Int) ) (and (= v_0 0) (|filter_acc[0:3]| 0 v_1) (|make_intlist[0:1][0:1][0:1][0:0]| v_4 v_1 v_2 0) (|make_intlist[0:1][0:0]| v_4 v_1)))
  )
)
