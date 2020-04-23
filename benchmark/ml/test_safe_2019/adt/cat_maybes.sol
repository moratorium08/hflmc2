sat
(model
  (define-fun |length[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (>= (* (- 1) v_1) 0)
  )
  (define-fun |make_abst_option_list[0:1][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    true
  )
  (define-fun |length_27[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |length_27[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (>= v_1 0)
  )
  (define-fun |make_abst_option_list[0:1][0:1][0:1][0:1]|
    ( (v_0 Int) (v_1 Int) (v_2 Int) (v_3 Bool) (v_4 Int) ) Bool
    true
  )
  (define-fun |cat_maybes[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |cat_maybes[0:2][0:0]|
    ( (v_0 Int) (v_1 Int) ) Bool
    (>= (* (- 1) v_1) 0)
  )
  (define-fun |length[0:0]|
    ( (v_0 Int) ) Bool
    (>= (* (- 1) v_0) 0)
  )
  (define-fun |fail_153[0:0]|
    ( (v_0 Int) ) Bool
    false
  )
  (define-fun |make_abst_option_list[0:0]|
    ( (v_0 Int) ) Bool
    true
  )
  (define-fun |cat_maybes[0:1][0:1][0:1]|
    ( (v_0 Int) (v_1 Int) (v_2 Bool) (v_3 Int) ) Bool
    (exists ( (v_4 Int) (v_5 Int) ) (and (|make_abst_option_list[0:1][0:0]| v_4 v_0) (|cat_maybes[0:0]| v_0) (|make_abst_option_list[0:1][0:1][0:1][0:1]| v_4 v_0 v_1 v_2 0) (|length_27[0:2][0:0]| v_0 v_5)))
  )
)
