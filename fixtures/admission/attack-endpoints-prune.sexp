(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l2 (kind attested) (provenance user))
    (meta l3 (kind certified) (provenance user)))
  (table
    (row (kind observed) (provenance user) (decision quarantine)))
  (unit
    (sigma (sorts) (cons) (preds (pred a (args)) (pred b (args)) (pred c (args)) (pred d (args))))
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a))
      (leaf l2 (atom b))
      (leaf l3 (atom c)))
    (args
      (arg a1 (leaf l1))
      (arg a2 (leaf l2))
      (arg a3 (leaf l3)))
    (attacks
      (rebut a1 a2)
      (undercut a3 a1 (pos (prem 0)))
      (rebut a2 a3)))
  (expected
    (accepted
      (audit
        (leaves (leaf-row l1 (cause policy)))
        (args a1)
        (attacks
          (rebut a1 a2)
          (undercut a3 a1 (pos (prem 0))))))))
