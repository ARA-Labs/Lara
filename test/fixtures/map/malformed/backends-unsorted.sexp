; A backend selection that is not strictly ascending by (id, version), so
; one selection would have more than one spelling.
(map-check-input@1
  (policy empirical-v1)
  (backends (backend ra 1) (backend nd 1))
  (members
    (member paper_a m.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions)))))
  (alignments))
