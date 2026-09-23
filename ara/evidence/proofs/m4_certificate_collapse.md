# Certificate collapse changes an accepted observation

The source has two distinct defeasible wrappers around certificates that differ
only in payload. A declared root undercut hits one wrapper. After payload
collapse, structural merging removes the surviving unattacked support. The same
export is justified before collapse and defeated after collapse. Both units pass
the checker, and the source has the full declarative `Admissible` proof.

The bundled theorem contains every parametricity premise except `RelInj`,
negates that premise, and negates observation equality. It uses the same sound
fixture registry on both sides. The adapter interprets every payload as ND's
fixed free-slot certificate and inherits ND soundness and dependency accounting;
its direct replay is proved equal to ND replay before use.

The relation is functional but non-injective. The result refutes deleting
`RelInj` wholesale, not every weakening of it, and does not separate the
functional and relational theorems' expressive strength. The contrary table is
empty; attack completeness therefore does not force the undeclared undercut.
Production ND decoding and corpus/freeze contracts remain unchanged.

## Sources

- `theorem observations :` ← `lean/Lara/Examples/CertificateCollapse.lean:88` «theorem observations :» [result]
- `theorem admissible : Admissible registry ctx sourceFrag where` ← `lean/Lara/Examples/CertificateCollapse.lean:157` «theorem admissible : Admissible registry ctx sourceFrag where» [result]
- `theorem relInj_observationally_necessary :` ← `lean/Lara/Examples/CertificateCollapse.lean:187` «theorem relInj_observationally_necessary :» [result]

## Verification

- `lake build`: Build completed successfully (159 jobs); existing upstream linter warnings replayed.
- `check-axcheck-coverage.py`: AxCheck coverage passed (12 declarations).
- Full `lake env lean AxCheck.lean` and `scripts/check-axioms.sh`: Axiom audit passed.
- Independent agent review confirmed the premise bundle, source admissibility,
  observation values, backend obligations, and import/audit coverage.

## Rejected construction

An undermine of the shared premise leaf would cover both wrappers before
collapse. Root contrary attacks would force the omitted symmetric attack via
`SideOk.attack_complete`. The declared root undercut avoids both problems.
