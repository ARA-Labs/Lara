(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l2 (kind attested) (provenance user)))
  (table
    (row (kind attested) (provenance user) (decision reject)))
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
    (rejected (leaf l2) (kind attested) (provenance user) (decision reject))))
