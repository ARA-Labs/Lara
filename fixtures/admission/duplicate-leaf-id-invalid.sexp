(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l1 (kind assumed) (provenance ai)))
  (table)
  (unit
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a)))
    (args)
    (attacks))
  (expected
    (invalid (duplicate-leaf-id l1))))
