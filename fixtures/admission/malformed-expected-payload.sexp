(admission
  (metas
    (meta l1 (kind observed) (provenance user)))
  (table)
  (unit
    (sigma (sorts) (cons) (preds (pred a (args)) (pred b (args)) (pred c (args)) (pred d (args))))
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
