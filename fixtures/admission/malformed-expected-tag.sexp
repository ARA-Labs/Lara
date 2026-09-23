(admission
  (metas
    (meta l1 (kind observed) (provenance user)))
  (table)
  (unit
    (sigma (sorts) (cons) (preds (pred a (args)) (pred b (args)) (pred c (args)) (pred d (args))))
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a)))
    (args)
    (attacks))
  (oracle
    (accepted (audit (leaves) (args) (attacks)))))
