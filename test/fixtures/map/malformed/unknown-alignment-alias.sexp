; An alignment naming a member alias the envelope does not declare.
(map-check-input@1
  (policy empirical-v1)
  (backends (backend nd 1))
  (members
    (member paper_a m.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions)))))
  (alignments (alignment (ref paper_a c1 whole) (ref paper_z c1 whole) same (author r) (audit-status unreviewed) (rationale ""))))
