(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l2 (kind attested) (provenance user))
    (meta l3 (kind certified) (provenance user))
    (meta l4 (kind assumed) (provenance ai)))
  (table
    (row (kind observed) (provenance user) (decision quarantine)))
  (unit
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a))
      (leaf l2 (atom b))
      (leaf l3 (atom c))
      (leaf l4 (atom d)))
    (args
      (arg a1 (leaf l1))
      (arg a2 (inst r (subst) (premises (leaf l1)) (discharges) (holes) (assurance none)))
      (arg a3 (inst r2 (subst) (premises) (discharges (q1 (leaf l1))) (holes) (assurance none)))
      (arg a4 (leaf l2)))
    (attacks))
  (expected
    (accepted
      (audit
        (leaves (leaf-row l1 (cause policy)))
        (args a1 a2 a3)
        (attacks)))))
