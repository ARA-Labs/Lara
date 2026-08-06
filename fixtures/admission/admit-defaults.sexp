(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l2 (kind assumed) (provenance ai)))
  (table
    (row (kind observed) (provenance user) (decision admit)))
  (unit
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a))
      (leaf l2 (atom b)))
    (args
      (arg a1 (leaf l1))
      (arg a2 (leaf l2)))
    (attacks))
  (expected
    (accepted (audit (leaves) (args) (attacks)))))
