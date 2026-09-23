(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l2 (kind attested) (provenance user)))
  (table
    (row (kind observed) (provenance user) (decision quarantine)))
  (unit
    (sigma (sorts) (cons) (preds (pred a (args)) (pred b (args)) (pred c (args)) (pred d (args))))
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a))
      (leaf l2 (atom b)))
    (args
      (arg a1 (leaf l1))
      (arg a2 (leaf l2)))
    (attacks
      (rebut a1 a2))
    (groups
      quarantine
      (group g1 (l1 l2))))
  (expected
    (accepted
      (audit
        (leaves
          (leaf-row l1 (cause policy) (cause (group g1)))
          (leaf-row l2 (cause (group g1))))
        (args a1 a2)
        (attacks
          (rebut a1 a2))))))
