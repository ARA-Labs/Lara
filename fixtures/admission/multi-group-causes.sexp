(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l2 (kind attested) (provenance user))
    (meta l3 (kind certified) (provenance user)))
  (table)
  (unit
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a))
      (leaf l2 (atom b))
      (leaf l3 (atom c)))
    (args
      (arg a1 (leaf l1))
      (arg a2 (leaf l2))
      (arg a3 (leaf l3)))
    (attacks)
    (groups
      quarantine
      (group g1 (l1 l2))
      (group g2 (l1 l3))))
  (expected
    (accepted
      (audit
        (leaves
          (leaf-row l1 (cause (group g1)) (cause (group g2)))
          (leaf-row l2 (cause (group g1)))
          (leaf-row l3 (cause (group g2))))
        (args a1 a2 a3)
        (attacks)))))
