# Backend mutation coverage — evaluation freeze v6

Measured from clean input commit `bc888a5d4b60438565bcf0922a8a3f04cfc645b8` on 2026-09-09.

Source: `measurements/frozen/ablation.json`, aggregate of each named ablation.

no-cq: count=655; missed-rejects=18; unchanged=637; missed classes: reject-IncompleteArgument=18.
no-typed: count=655; missed-rejects=37; unchanged=618; missed classes: reject-MissingConflict=5, reject-R10=11, reject-R11=21.
no-conflict-scan: count=655; missed-rejects=5; unchanged=650; missed classes: reject-MissingConflict=5.

Source: `measurements/frozen/report.json`, aggregate.
Class match: 655/655. Haskell–Lean agreement: 655/655. Location match and primary: 480/480 each. Corpus replay: 60/60.

Added 27 S2 and 27 S9 mutants (22 verdict + 5 codec each). Compared all 541 old mutant bytes and manifest rows against 08ebe6a: unchanged. Compared all 601 old report rows on deterministic columns 1–15 and all old ablation rows: unchanged. The full input corpus is now 655 records.

Commands: `cabal exec -- runghc scripts/gen-mutants.hs --check`; `cabal test all --test-show-details=direct`; `bash scripts/differential.sh`; `bash scripts/admission-differential.sh`; `bash scripts/test-replay-tamper.sh`; Lean build and axiom audit; freeze-bundle unit tests; `make presentation-parity`; `ELAN_TOOLCHAIN=leanprover/lean4:v4.32.0 make measure`; `cabal exec -- runghc scripts/claim-support.hs`. All passed.

Differential: 669 verdict anchors and 66 codec negatives, zero failures. Admission: 20/20. Freeze-bundle: 4/4. Presentation parity: 78 rows. Independent review found no actionable defects.

The certificate additions exercise backend payload decoding (R13) and theory allowlisting (R7), not every semantic branch. No new soundness result is claimed. Timing comparisons with v5 are invalid across the different machines. The v6 publication tag is reserved for the eventual merge commit; this record does not claim publication.
