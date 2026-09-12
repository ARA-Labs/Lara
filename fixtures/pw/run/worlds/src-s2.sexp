; Context src, world s2: the q argument alone, so q is justified and p is gap.
(check-input
  (replay-id (core lara-core@0.2) (policy pw-src) (backends (backend nd 1))
    (theories) (artifact pw-src-s2))
  (unit
    (sigma (sorts Item) (cons (con z (args) Item))
      (preds (pred p (args)) (pred q (args)) (pred s (args)) (pred t (args Item))
        (pred u (args))))
    (policy (rules) (contraries (contrary (apat q) (apat p))) (exceptions))
    (theories)
    (leaves (leaf l1 (atom p)) (leaf l2 (atom q)))
    (args (arg a2 (leaf l2)))
    (attacks)
    (queries)))
