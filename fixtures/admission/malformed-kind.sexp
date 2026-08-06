(admission
  (metas
    (meta l1 (kind observed) (provenance user)))
  (table
    (row (kind bogus) (provenance user) (decision admit)))
  (unit
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a)))
    (args)
    (attacks))
  (expected
    (accepted (audit (leaves) (args) (attacks)))))
