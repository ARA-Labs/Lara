; This is the existing CLI boundary, NOT the Lean structural-contract witness.
; Expected: world-input at tgt, before any bridge is loaded.
(pw-run 1
  (worlds (world src s (lara "../../../examples/axiom-withdrawal/admitted.lara"))
          (world tgt t (lara "../../../examples/axiom-withdrawal/withdrawn.lara")))
  (edges)
  (comparisons)
  (pw-surface 1 (bridges) (queries)))
