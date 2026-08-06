(admission
  (metas
    (meta l1 (kind observed) (provenance user))
    (meta l2 (kind attested) (provenance user)))
  (table
    (row (kind observed) (provenance user) (decision quarantine)))
  (unit
    (policy (rules) (contraries) (exceptions))
    (leaves
      (leaf l1 (atom a))
      (leaf l2 (atom b)))
    (args
      (arg a1 (leaf l1))
      (arg a2 (leaf l2))
      (arg a3 (leaf l2)))
    (attacks
      (rebut a1 a2)
      (rebut a2 a3)))
  (expected
    (accepted
      (audit
        (leaves (leaf-row l1 (cause policy)))
        (args a1)
        (attacks
          (rebut a1 a2))))))
