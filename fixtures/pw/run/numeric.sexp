; Numeric literals keep their authored text on the wire and are compared
; under the production canonicalizer: 01.00, +1 and 1.0 denote one numeral.
; The result echoes each claim exactly as written.
(pw-run 1
  (worlds
    (world n0 n (inline
      (check-input
        (replay-id (core lara-core@0.2) (policy pw-num) (backends (backend nd 1))
          (theories) (artifact pw-num-n0))
        (unit
          (sigma (sorts) (cons) (preds (pred m (args Num))))
          (policy (rules) (contraries) (exceptions))
          (theories)
          (leaves (leaf l1 (atom m (num 1.0))))
          (args (arg a1 (leaf l1)))
          (attacks)
          (queries (atom m (num 1))))))))
  (edges (edge same n0 n0 accepted))
  (comparisons (compare same n0 (atom m (num +1))) (compare same n0 (atom m (num 2))))
  (pw-surface 1
    (bridges
      (bridge same n n (symbols (pred m m)) (leaves) (clauses leaf-ok rule-ok cert-ok)))
    (queries
      (pose n (status justified (atom m (num 01.00))))
      (pose n (status justified (atom m (num 2))))
      (pose n (box same (status justified (atom m (num -0001.000))))))))
