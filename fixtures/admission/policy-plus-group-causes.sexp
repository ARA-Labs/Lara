(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l2 (kind attested) (provenance user))
    (meta l3 (kind certified) (provenance user)))
  (table
    (row (kind observed) (provenance user) (decision quarantine)))
  (unit
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a))
      (leaf l2 (atom b))
      (leaf l3 (atom b)))
    (args
      (arg a1 (leaf l1))
      (arg a2 (leaf l2))
      (arg a3 (leaf l3)))
    (attacks)
    (groups
      quarantine
      (group g1 (l1 l2))
      (group g2 (l2 l3))))
  (expected
    (accepted
      (audit
        (leaves
          (leaf-row l1 (cause policy) (cause (group g1)))
          (leaf-row l2 (cause (group g1))))
        (args a1 a2)
        (attacks)))))
