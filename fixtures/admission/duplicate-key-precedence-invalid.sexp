(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l1 (kind assumed) (provenance ai)))
  (table
    (row (kind observed) (provenance user) (decision admit))
    (row (kind observed) (provenance user) (decision reject)))
  (unit
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a)))
    (args)
    (attacks))
  (expected
    (invalid (duplicate-key observed user))))
