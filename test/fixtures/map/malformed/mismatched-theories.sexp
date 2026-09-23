; Two members whose units carry different backend theory payloads. The
; contract compares label AND payload, so one member proving under a theory
; the other never saw is refused.
(map-check-input@1
  (policy empirical-v1)
  (backends (backend nd 1))
  (members
    (member paper_a m.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions)) (theories (theory sha256:t1 (atom p (con a))))))
    (member paper_b n.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions)))))
  (alignments))
