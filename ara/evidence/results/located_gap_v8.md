# Located-gap follow-ups (`lara-core@0.3`, amended) — evaluation freeze v8

Measured from clean input commit `59a94c866c2214ef1042c3b83fb6480da3bcf17d` on 2026-10-05 (branch `feat/located-gap`, PR #12), after issues #11, #13, #14, #15 and #16 landed.

Source: `measurements/frozen/ablation.tsv`, aggregate of each named ablation.

no-cq: count=660; missed-rejects=0; new-rejects=0; changed=66; status-shifts=65 (gap->justified=57, gap->defeated=6, gap->contested=2, justified->contested=1); changed by kind: corpus=48, mutant=18.
no-cq corpus only: changed=48/48; shifted statuses gap->justified=46, gap->defeated=2.
no-typed: count=660; missed-rejects=39; new-rejects=0; missed classes: reject-MissingConflict=5, reject-R10=13, reject-R11=21.
no-conflict-scan: count=660; missed-rejects=5; new-rejects=0; missed classes: reject-MissingConflict=5.

Source: `measurements/frozen/report.tsv`, aggregate.
Class match: 660/660. Haskell–Lean agreement: 660/660. Location match and primary: 485/485 each. Corpus replay: 60/60.

Expected classes (report.tsv): accept-gap=9, accept-located-hole=66, reject-R10=13, reject-R4=37 (v7: 57, 18, 11, 34); all other classes unchanged.

Claim support (`measurements/frozen/claim-support.json`): all leaves 171 (observed 65); load-bearing leaves 38; typed attacks 5; dead-end-sourced 4; binding-audit subjects 1 strict-step + 3 typed-attack.

Gates: `make local-gates` pass (differential 683 verdict anchors + 66 codec negatives, zero failures; mutant differential 1651/1651; admission 20/20; map conformance 5 anchors; update differential 174 decisions); `gen-mutants.hs` 600 verified mutants; walking-skeleton replay byte-identical.
