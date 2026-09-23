(admission
  (metas
    (meta l2 (kind assumed) (provenance ai))
    (meta l1 (kind observed) (provenance user)))
  (table)
  (unit
    (sigma (sorts) (cons) (preds (pred a (args)) (pred b (args)) (pred c (args)) (pred d (args))))
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a))
      (leaf l2 (atom b)))
    (args)
    (attacks))
  (expected
    (invalid metadata-leaf-misalignment)))
