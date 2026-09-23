; Context tgt, world t0: the q argument alone. tgt declares r and not s, and
; declares u as unary where src declares it nullary.
(check-input
  (replay-id (core lara-core@0.2) (policy pw-tgt) (backends (backend nd 1))
    (theories) (artifact pw-tgt-t0))
  (unit
    (sigma (sorts Item) (cons (con z (args) Item))
      (preds (pred p (args)) (pred q (args)) (pred r (args)) (pred t (args Item))
        (pred u (args Item))))
    (policy (rules) (contraries) (exceptions))
    (theories)
    (leaves (leaf l1 (atom p)) (leaf l2 (atom q)))
    (args (arg a2 (leaf l2)))
    (attacks)
    (queries)))
