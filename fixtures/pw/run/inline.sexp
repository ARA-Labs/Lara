; The PW0 T7 witness as a run file with inline worlds: one context, an
; endobridge, and one accepted edge from w0 (p justified) to w1 (the same p
; argument plus an unattacked attacker, so p is defeated). Comparing p along
; the edge reports defeated although p is justified at the source world.
(pw-run 1
  (worlds
    (world w0 c (inline
      (check-input
        (replay-id (core lara-core@0.2) (policy pw-t7) (backends (backend nd 1))
          (theories) (artifact pw-t7-w0))
        (unit
          (sigma (sorts) (cons) (preds (pred p (args)) (pred q (args))))
          (policy (rules) (contraries (contrary (apat q) (apat p))) (exceptions))
          (theories)
          (leaves (leaf l1 (atom p)) (leaf l2 (atom q)))
          (args (arg a1 (leaf l1)))
          (attacks)
          (queries (atom p))))))
    (world w1 c (inline
      (check-input
        (replay-id (core lara-core@0.2) (policy pw-t7) (backends (backend nd 1))
          (theories) (artifact pw-t7-w1))
        (unit
          (sigma (sorts) (cons) (preds (pred p (args)) (pred q (args))))
          (policy (rules) (contraries (contrary (apat q) (apat p))) (exceptions))
          (theories)
          (leaves (leaf l1 (atom p)) (leaf l2 (atom q)))
          (args (arg a1 (leaf l1)) (arg a2 (leaf l2)))
          (attacks (undermine a2 a1 (pos)))
          (queries (atom p)))))))
  (edges (edge e w0 w1 accepted))
  (comparisons (compare e w0 (atom p)) (compare e w1 (atom p)))
  (pw-surface 1
    (bridges
      (bridge e c c (symbols (pred p p) (pred q q)) (leaves) (clauses leaf-ok rule-ok cert-ok)))
    (queries
      (pose c (status justified (atom p)))
      (pose c (dia e (status defeated (atom p))))
      (pose c (box e (box e (status gap (atom q))))))))
