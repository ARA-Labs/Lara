(admission
  (metas
    (meta l1 (kind observed) (provenance user)))
  (table)
  (unit
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a)))
    (args
      (arg a1 (leaf l1)))
    (attacks))
  (expected
    (accepted
      (audit
        (leaves (leaf-row l1 nonsense))
        (args)
        (attacks)))))
