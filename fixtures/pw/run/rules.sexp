; T6's decidable clause at work: both contexts declare the defeasible rule
; r1 : p => q, so a bridge carrying p and q satisfies rule-ok. Mapping q to a
; symbol the target's r1 does not conclude, or dropping q, fails it
; (scripts/check-pw-conformance.py mutates this file to both).
(pw-run 1
  (worlds
    (world a0 a (inline
      (check-input
        (replay-id (core lara-core@0.2) (policy pw-rules) (backends (backend nd 1))
          (theories) (artifact pw-rules-a0))
        (unit
          (sigma (sorts) (cons) (preds (pred p (args)) (pred q (args))))
          (policy
            (rules (rule r1 (mode defeasible) (params) (premises (apat p))
              (conclusion (apat q)) (questions) (allow-trusted false) (certifiers)))
            (contraries) (exceptions))
          (theories)
          (leaves (leaf l1 (atom p)))
          (args (arg x1 (leaf l1))
            (arg x2 (inst r1 (subst) (premises (leaf l1)) (discharges) (holes)
              (assurance none))))
          (attacks)
          (queries)))))
    (world b0 b (inline
      (check-input
        (replay-id (core lara-core@0.2) (policy pw-rules) (backends (backend nd 1))
          (theories) (artifact pw-rules-b0))
        (unit
          (sigma (sorts) (cons) (preds (pred p (args)) (pred q (args))))
          (policy
            (rules (rule r1 (mode defeasible) (params) (premises (apat p))
              (conclusion (apat q)) (questions) (allow-trusted false) (certifiers)))
            (contraries) (exceptions))
          (theories)
          (leaves (leaf l1 (atom p)))
          (args (arg y1 (leaf l1)))
          (attacks)
          (queries))))))
  (edges (edge ab a0 b0 accepted))
  (comparisons (compare ab a0 (atom q)) (compare ab a0 (atom p)))
  (pw-surface 1
    (bridges
      (bridge ab a b (symbols (pred p p) (pred q q)) (leaves)
        (clauses leaf-ok rule-ok cert-ok)))
    (queries
      (pose a (status justified (atom q)))
      (pose a (dia ab (status gap (atom q))))
      (pose b (status justified (atom p))))))
