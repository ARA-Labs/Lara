; The host provides src/tgt contexts and one checked world in each.
(pw-surface 1
  (bridges
    (bridge b src tgt
      (symbols (pred q q) (pred p p) (con z z))
      (leaves)
      (clauses leaf-ok rule-ok cert-ok)))
  (queries
    (pose src (dia b (status justified (atom q))))
    (pose src (box b (status gap (atom p))))
    (pose src (and (status justified (atom p))
      (not (dia b (status defeated (atom q))))))))
