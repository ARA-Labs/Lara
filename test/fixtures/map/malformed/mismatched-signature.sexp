; Two members whose units carry different signatures. On the .laramap door
; this is impossible (every member was compared to the manifest's policy);
; in a hand-written envelope it has to be refused here.
(map-check-input@1
  (policy empirical-v1)
  (backends (backend nd 1))
  (members
    (member paper_a m.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions))))
    (member paper_b n.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S T) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions)))))
  (alignments))
