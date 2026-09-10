; A member whose declared path is the empty atom. The path is what the
; composite verdict reports a member by, so an empty one names nothing --
; and BOTH decoders must say so, which is the point of this anchor: the
; Haskell decoder refused it from the start and the Lean one did not, so a
; verdict came out of one driver and an error out of the other.
(map-check-input@1
  (policy empirical-v1)
  (backends (backend nd 1))
  (members
    (member paper_a "" (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions))))
    (member paper_b n.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions)))))
  (alignments))
