; Two members whose units carry different policy rules -- a redefinition
; under a shared policy id, which is exactly what comparing structures rather
; than names is for.
(map-check-input@1
  (policy empirical-v1)
  (backends (backend nd 1))
  (members
    (member paper_a m.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions))))
    (member paper_b n.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules (rule r1 (mode defeasible) (params) (premises) (conclusion (apat p (var X))) (questions) (allow-trusted false) (certifiers))) (contraries) (exceptions)))))
  (alignments))
