; Context tgt, world t1: the p argument alone.
(check-input
  (replay-id (core lara-core@0.2) (policy pw-tgt) (backends (backend nd 1))
    (theories) (artifact pw-tgt-t1))
  (unit
    (sigma (sorts Item) (cons (con z (args) Item))
      (preds (pred p (args)) (pred q (args)) (pred r (args)) (pred t (args Item))
        (pred u (args Item))))
    (policy (rules) (contraries) (exceptions))
    (theories)
    (leaves (leaf l1 (atom p)) (leaf l2 (atom q)))
    (args (arg a1 (leaf l1)))
    (attacks)
    (queries)))
