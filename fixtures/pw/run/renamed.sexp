; T6's rule clause under a renaming symbol map. Context b states rule r1 over
; renamed vocabulary: predicates p, q and ok become p2, q2 and ok2, and the
; constructors f and z become g and z2. The bridge carries exactly that
; renaming, so rule-ok holds only if r1's premise (with its constructor
; sub-pattern), its conclusion and its critical question's answer all
; translate to b's r1. scripts/check-pw-conformance.py breaks each translated
; position in turn.
(pw-run 1
  (worlds
    (world a0 a (inline
      (check-input
        (replay-id (core lara-core@0.2) (policy pw-renamed) (backends (backend nd 1))
          (theories) (artifact pw-renamed-a0))
        (unit
          (sigma (sorts Item) (cons (con z (args) Item) (con f (args Item) Item))
            (preds (pred p (args Item)) (pred q (args Item)) (pred ok (args Item))))
          (policy
            (rules (rule r1 (mode defeasible) (params X) (premises (apat p (con f (var X))))
              (conclusion (apat q (var X)))
              (questions (question safe (apat ok (var X)) optional))
              (allow-trusted false) (certifiers)))
            (contraries) (exceptions))
          (theories)
          (leaves (leaf l1 (atom p (con f (con z)))))
          (args (arg x1 (leaf l1)))
          (attacks)
          (queries)))))
    (world b0 b (inline
      (check-input
        (replay-id (core lara-core@0.2) (policy pw-renamed) (backends (backend nd 1))
          (theories) (artifact pw-renamed-b0))
        (unit
          (sigma (sorts Item) (cons (con z2 (args) Item) (con g (args Item) Item))
            (preds (pred p2 (args Item)) (pred q2 (args Item)) (pred ok2 (args Item))))
          (policy
            (rules (rule r1 (mode defeasible) (params X) (premises (apat p2 (con g (var X))))
              (conclusion (apat q2 (var X)))
              (questions (question safe (apat ok2 (var X)) optional))
              (allow-trusted false) (certifiers)))
            (contraries) (exceptions))
          (theories)
          (leaves (leaf l1 (atom p2 (con g (con z2)))))
          (args (arg y1 (leaf l1)))
          (attacks)
          (queries))))))
  (edges (edge ab a0 b0 accepted))
  (comparisons (compare ab a0 (atom p (con f (con z)))) (compare ab a0 (atom q (con z))))
  (pw-surface 1
    (bridges
      (bridge ab a b (symbols (pred p p2) (pred q q2) (pred ok ok2) (con f g) (con z z2))
        (leaves) (clauses leaf-ok rule-ok cert-ok)))
    (queries
      (pose a (dia ab (status justified (atom p2 (con g (con z2))))))
      (pose b (status gap (atom q2 (con z2)))))))
