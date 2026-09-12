; Two overlapping fields. src declares s and a nullary u; tgt declares r and a
; unary u. Both declare t(Item) and the constructor z. Worlds are check-input
; envelopes read relative to this file.
;
; b    : src -> tgt carries p q s t u, and not the constructor z.
; back : tgt -> src carries q p t and z.
;
; Queries are answered at every world of their context, in declaration order.
; Comparisons cover every result kind: a two-status profile, one filtered by a
; rejected edge, both incomparability reasons that survive posing, and all
; five posing faults.
(pw-run 1
  (worlds
    (world s0 src (file "worlds/src-s0.sexp"))
    (world s1 src (file "worlds/src-s1.sexp"))
    (world s2 src (file "worlds/src-s2.sexp"))
    (world t0 tgt (file "worlds/tgt-t0.sexp"))
    (world t1 tgt (file "worlds/tgt-t1.sexp")))
  (edges
    (edge b s0 t0 accepted)
    (edge b s0 t1 rejected)
    (edge b s1 t0 accepted)
    (edge b s1 t1 accepted)
    (edge back t0 s1 accepted)
    (edge back t1 s0 rejected))
  (comparisons
    (compare b s1 (atom p))
    (compare b s0 (atom q))
    (compare b s2 (atom q))
    (compare back t1 (atom q))
    (compare b s0 (atom s))
    (compare b s0 (atom r))
    (compare b s0 (atom p (con z)))
    (compare b s0 (atom u))
    (compare back t0 (atom r))
    (compare b s0 (atom t (con z)))
    (compare back t0 (atom t (con z))))
  (pw-surface 1
    (bridges
      (bridge b src tgt
        (symbols (pred p p) (pred q q) (pred s s) (pred t t) (pred u u))
        (leaves)
        (clauses leaf-ok rule-ok cert-ok))
      (bridge back tgt src
        (symbols (pred q q) (pred p p) (pred t t) (con z z))
        (leaves)
        (clauses leaf-ok rule-ok cert-ok)))
    (queries
      (pose src (dia b (status justified (atom p))))
      (pose src (box b (status gap (atom p))))
      (pose src (box b (dia back (status defeated (atom p)))))
      (pose tgt (dia back (status justified (atom q))))
      (pose src (and (status gap (atom p)) (not (dia b (top))))))))
