; One member declaring the same claim name twice. (alias, claim name) is the
; map's reporting handle and resolution is a first-wins lookup, so a repeat
; would give one status two meanings.
(map-check-input@1
  (policy empirical-v1)
  (backends (backend nd 1))
  (members
    (member paper_a m.lara (artifact sha256:m) (claims (claim c1 (atom p (con a))) (claim c1 (atom q (con b)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions)))))
  (alignments))
