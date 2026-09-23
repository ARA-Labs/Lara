(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l2 (kind assumed) (provenance ai)))
  (table
    (row (kind observed) (provenance user) (decision admit))
    (row (kind observed) (provenance user) (decision reject)))
  (unit
    (sigma (sorts) (cons) (preds (pred a (args)) (pred b (args)) (pred c (args)) (pred d (args))))
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a))
      (leaf l2 (atom b)))
    (args
      (arg a1 (leaf l1)))
    (attacks))
  (expected
    (invalid (duplicate-key observed user))))
