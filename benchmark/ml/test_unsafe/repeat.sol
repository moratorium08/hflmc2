sat
(model
  (define-fun |fail_17[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |repeat[0:2]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (and (>= v_0 1) (= v_1 0))
  )
  (define-fun |repeat[0:3][0:0]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) ) Bool
    (and (= (+ v_2 (* (- 1) v_1)) 0) (= v_0 0) (|repeat[0:2]| 0 v_2))
  )
)
