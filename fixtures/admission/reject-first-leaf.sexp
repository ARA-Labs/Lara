(admission
  (metas
    (meta e_assumed (kind assumed) (provenance ai))
    (meta l2 (kind attested) (provenance user)))
  (table
    (row (kind assumed) (provenance ai) (decision reject)))
  (unit
    (sigma (sorts) (cons) (preds (pred a (args)) (pred b (args)) (pred c (args)) (pred d (args))))
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf e_assumed (atom a))
      (leaf l2 (atom b)))
    (args
      (arg a1 (leaf e_assumed))
      (arg a2 (leaf l2)))
    (attacks))
  (expected
    (rejected (leaf e_assumed) (kind assumed) (provenance ai) (decision reject))))
