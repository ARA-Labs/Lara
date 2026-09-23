; Context src, world s1: the same p argument plus an unattacked q attacker, so
; p is defeated and q is justified (the PW0 T7 target world).
(check-input
  (replay-id (core lara-core@0.2) (policy pw-src) (backends (backend nd 1))
    (theories) (artifact pw-src-s1))
  (unit
    (sigma (sorts Item) (cons (con z (args) Item))
      (preds (pred p (args)) (pred q (args)) (pred s (args)) (pred t (args Item))
        (pred u (args))))
    (policy (rules) (contraries (contrary (apat q) (apat p))) (exceptions))
    (theories)
    (leaves (leaf l1 (atom p)) (leaf l2 (atom q)))
    (args (arg a1 (leaf l1)) (arg a2 (leaf l2)))
    (attacks (undermine a2 a1 (pos)))
    (queries)))
