# Located gap (`lara-core@0.3`) — evaluation freeze v7

Measured from clean input commit `be82e970f3d26647a9c8accb084c452544851d6f` on 2026-10-05 (branch `feat/located-gap`, PR #12).

Source: `measurements/frozen/ablation.json`, aggregate of each named ablation.

no-cq: count=655; missed-rejects=0; new-rejects=0; status-shifts=17; unchanged=637; changed class: accept-located-hole=18 (shifted statuses gap->justified=11, gap->defeated=4, gap->contested=2, justified->contested=1).
no-typed: count=655; missed-rejects=37; new-rejects=0; unchanged=618; missed classes: reject-MissingConflict=5, reject-R10=11, reject-R11=21.
no-conflict-scan: count=655; missed-rejects=5; new-rejects=0; unchanged=650; missed classes: reject-MissingConflict=5.

Source: `measurements/frozen/report.json`, aggregate.
Class match: 655/655. Haskell–Lean agreement: 655/655. Location match and primary: 480/480 each. Corpus replay: 60/60.

Regeneration (`measurements/frozen/lara-core-0.3-regeneration-diffs.md`): exactly the 18 hole-obligation mutant rows move reject-IncompleteArgument -> accept-located-hole; every other manifest column is byte-identical; corpus verdict+status diff over 60 units is empty; mutant split 519 reject / 76 accept.

Gates: `cabal test all` pass; `gen-mutants.hs --check` 595 byte-identical; `make local-gates` pass (differential 677 verdict anchors + 66 codec negatives, zero failures; map conformance 5 anchors agree; PW conformance 102 cases; surface conformance 28 cases; axiom audit trio-only).
