(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l2 (kind attested) (provenance user))
    (meta l3 (kind certified) (provenance user))
    (meta l4 (kind assumed) (provenance ai)))
  (table)
  (unit
    (sigma (sorts) (cons) (preds (pred a (args)) (pred b (args)) (pred c (args)) (pred d (args))))
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a))
      (leaf l2 (atom b))
      (leaf l3 (atom c))
      (leaf l4 (atom c)))
    (args
      (arg a1 (leaf l1))
      (arg a2 (leaf l2))
      (arg a3 (leaf l3))
      (arg a4 (leaf l4)))
    (attacks
      (rebut a3 a1)
      (rebut a3 a4))
    (groups
      quarantine
      (group g1 (l1 l2))
      (group g2 (l3 l4))))
  (expected
    (accepted
      (audit
        (leaves
          (leaf-row l1 (cause (group g1)))
          (leaf-row l2 (cause (group g1))))
        (args a1 a2)
        (attacks
          (rebut a3 a1))))))
