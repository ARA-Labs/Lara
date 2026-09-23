; The inline T7 witness with .lara world sources (#327). Each world is a
; presentation program beside this file, elaborated by `lara pw` through the
; steps `lara check` takes on it alone. The Lean reference has no surface
; parser: `pw-run` on this file reports the first world as world-input, and
; the gate runs it on the document `lara pw-input` derives, whose worlds are
; the same envelopes inline. Expected answers are those of inline.sexp.
(pw-run 1
  (worlds
    (world w0 c (lara "worlds/w0.lara"))
    (world w1 c (lara "worlds/w1.lara")))
  (edges (edge e w0 w1 accepted))
  (comparisons (compare e w0 (atom p)) (compare e w1 (atom p)))
  (pw-surface 1
    (bridges
      (bridge e c c (symbols (pred p p) (pred q q)) (leaves) (clauses leaf-ok rule-ok cert-ok)))
    (queries
      (pose c (status justified (atom p)))
      (pose c (dia e (status defeated (atom p))))
      (pose c (box e (box e (status gap (atom q))))))))
