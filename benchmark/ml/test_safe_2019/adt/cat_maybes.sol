sat
(model
  (define-fun |length[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (or (= (+ v_0 (* (- 1) v_1)) 0) (and (>= (* (- 1) v_1) 0) (not (= (+ v_0 (* (- 1) v_1)) 0)) (>= (* (- 1) v_0) 1)))
  )
  (define-fun |make_abstoptionlist[0:1][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun |length_27[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |length_27[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (or (and (>= v_1 0) (>= (* (- 1) v_0) 1)) (and (>= v_0 0) (= (+ v_0 (* (- 1) v_1)) 0) (>= v_1 0)))
  )
  (define-fun |make_abstoptionlist[0:1][0:1][0:1][0:1]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Bool) (v_4 Int) ) Bool
    true
  )
  (define-fun |cat_maybes[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |cat_maybes[0:1][0:1][0:1]|
    ( (v_0 Int) (v_1 Int) (v_2 Bool) (v_3 Int) ) Bool
    true
  )
  (define-fun |cat_maybes[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (or (= v_1 0) (and (= (+ v_0 (* (- 1) v_1)) 0) (not (= v_1 0)) (>= (+ (* (- 1) v_1) (* 2 v_0)) 1)) (and (not (= (+ v_0 (* (- 1) v_1)) 0)) (not (= v_1 0)) (>= (+ v_0 (* (- 1) v_1)) 0) (>= (+ (* (- 1) v_1) (* 2 v_0)) 1)))
  )
  (define-fun |length[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |fail_153[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |make_abstoptionlist[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
)
