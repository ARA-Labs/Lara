; A member declaring one leaf id twice. No wire decoder on either side
; scans a unit's leaves for repeats -- they scan argument ids and groups --
; so this reaches the envelope decoder, which must refuse it: buildGamma is
; first-wins, so one leaf would silently shadow the other and every argument
; built on it would be checked against a proposition nobody wrote.
(map-check-input@1
  (policy empirical-v1)
  (backends (backend nd 1))
  (members
    (member paper_a m.lara (artifact sha256:m) (claims (claim c1 (atom p (con a)))) (unit (sigma (sorts S) (cons (con a (args) S) (con b (args) S)) (preds (pred p (args S)) (pred q (args S)))) (policy (rules) (contraries) (exceptions)) (leaves (leaf e1 (atom p (con a))) (leaf e1 (atom p (con b)))))))
  (alignments))
