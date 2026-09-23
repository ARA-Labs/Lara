; An alias outside nonempty ASCII [A-Za-z0-9_-]. The `:` is the character
; that frames a qualified key, so admitting it would make the framing
; ambiguous.
(map-check-input@1
  (policy empirical-v1)
  (backends (backend nd 1))
  (members
    (member pa:per m.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions)))))
  (alignments))
