; The inline T7 witness with duplicate-report groups that agree (#326). Both
; worlds declare l1 and l3 as two reports of p and group them; w0 supports p
; from the grouped report l3 and w1 from l1, under the two conflict modes. A
; consistent group quarantines nothing, so both worlds are checked exactly as
; declared and the run's answers are those of inline.sexp.
(pw-run 1
  (worlds
    (world w0 c (inline
      (check-input
        (replay-id (core lara-core@0.2) (policy pw-t7) (backends (backend nd 1))
          (theories) (artifact pw-groups-w0))
        (unit
          (sigma (sorts) (cons) (preds (pred p (args)) (pred q (args))))
          (policy (rules) (contraries (contrary (apat q) (apat p))) (exceptions))
          (theories)
          (leaves (leaf l1 (atom p)) (leaf l2 (atom q)) (leaf l3 (atom p)))
          (args (arg a1 (leaf l3)))
          (attacks)
          (queries (atom p))
          (groups quarantine (group g1 (l1 l3)))))))
    (world w1 c (inline
      (check-input
        (replay-id (core lara-core@0.2) (policy pw-t7) (backends (backend nd 1))
          (theories) (artifact pw-groups-w1))
        (unit
          (sigma (sorts) (cons) (preds (pred p (args)) (pred q (args))))
          (policy (rules) (contraries (contrary (apat q) (apat p))) (exceptions))
          (theories)
          (leaves (leaf l1 (atom p)) (leaf l2 (atom q)) (leaf l3 (atom p)))
          (args (arg a1 (leaf l1)) (arg a2 (leaf l2)))
          (attacks (undermine a2 a1 (pos)))
          (queries (atom p))
          (groups reject (group g1 (l1 l3))))))))
  (edges (edge e w0 w1 accepted))
  (comparisons (compare e w0 (atom p)) (compare e w1 (atom p)))
  (pw-surface 1
    (bridges
      (bridge e c c (symbols (pred p p) (pred q q)) (leaves) (clauses leaf-ok rule-ok cert-ok)))
    (queries
      (pose c (status justified (atom p)))
      (pose c (dia e (status defeated (atom p))))
      (pose c (box e (box e (status gap (atom q))))))))
