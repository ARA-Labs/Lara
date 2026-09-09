# Generated mutation suite (M5 tracker #48, T1)

GENERATED — do not edit. Regenerate with:

    cabal exec -- runghc scripts/gen-mutants.hs

Every file is derived from the committed worked-example anchors
(`examples/<NAME>/example.core.sexp`, bases: A B E1 E2 E3 E4 E5 S1 S2 S9)
and the 60 committed corpus-unit anchors
(`corpus-units/<artifact>/<claim_id>/unit.core.sexp`, base label
`<artifact>.<claim_id>`), by the seeded operators of `Lara.Mutate` (seed 20260801),
verified against the production checker at generation time, re-verified on
every `cabal test` run (`test/MutationSpec.hs`: specified outcomes, seeded
reproducibility, class coverage, corpus sweep budget), and held
byte-identical across the Haskell and Lean drivers by
`scripts/differential.sh` (`malformed/` is the negative half: both drivers
exit 2 with no verdict AND the per-operator stderr diagnostic pinned in the
manifest's hs-diagnostic and lean-diagnostic columns, so a deleted codec
check cannot stay green via a different downstream failure).

Total mutants: 595

| expected outcome | mutants |
| --- | --- |
| `accept-all-contested` | 4 |
| `accept-contested` | 9 |
| `accept-defeated` | 18 |
| `accept-evidence-blocked` | 9 |
| `accept-gap` | 9 |
| `accept-justified` | 9 |
| `codec-reject` | 57 |
| `reject-IncompleteArgument` | 18 |
| `reject-MissingConflict` | 5 |
| `reject-R1` | 71 |
| `reject-R10` | 11 |
| `reject-R11` | 21 |
| `reject-R12` | 44 |
| `reject-R13` | 49 |
| `reject-R2` | 125 |
| `reject-R3` | 21 |
| `reject-R4` | 34 |
| `reject-R5` | 18 |
| `reject-R6` | 18 |
| `reject-R7` | 24 |
| `reject-R9` | 21 |

| mutation family | mutants |
| --- | --- |
| `accept-verdict` | 54 |
| `bad-attack-targets` | 37 |
| `certificate-tampering` | 73 |
| `codec-corruption` | 57 |
| `cycles` | 4 |
| `data-integrity` | 21 |
| `hidden-policy-extension` | 65 |
| `localization` | 35 |
| `open-obligations` | 54 |
| `signature` | 125 |
| `undeclared-leaves` | 29 |
| `wrong-formulas` | 41 |

## Corpus sweep (uniform derived-applicability, B = 12)

Per rejection operator over the corpus units: how many bases carry ≥1
site (applicable) and how many were selected (all when ≤ B, else B
picked by the operator-keyed stream). Two operators find no corpus
site and are recorded as 0/0: `drop-covering-attack` (only three
corpus units declare an attack at all, and none of those attacks
covers a contrary pair, so deleting one leaves the completeness scan
with nothing to report) and `twin-support-defect` (no corpus unit
carries wrong-premise sites at two distinct arguments).

| corpus operator | applicable bases | selected |
| --- | --- | --- |
| `undeclared-leaf` | 13 | 12 |
| `hidden-rule` | 13 | 12 |
| `hidden-contrary` | 60 | 12 |
| `wrong-subst-domain` | 13 | 12 |
| `wrong-premise` | 13 | 12 |
| `open-obligation` | 12 | 12 |
| `hole-obligation` | 12 | 12 |
| `wrong-discharge` | 12 | 12 |
| `trusted-assurance` | 12 | 12 |
| `cert-theory-swap` | 1 | 1 |
| `cert-payload-tamper` | 1 | 1 |
| `cert-wrong-fraction` | 1 | 1 |
| `bad-attack-position` | 3 | 3 |
| `unlicensed-attack` | 13 | 12 |
| `drop-covering-attack` | 0 | 0 |
| `group-conflict` | 55 | 12 |
| `retract-rule` | 13 | 12 |
| `twin-support-defect` | 0 | 0 |
| `cross-stage-defect` | 3 | 3 |
| `undeclared-pred` | 60 | 12 |
| `wrong-pred-arity` | 60 | 12 |
| `wrong-arg-sort` | 60 | 12 |
| `undeclared-con` | 60 | 12 |
| `wrong-theta-sort` | 13 | 12 |
| `out-of-scope-var` | 60 | 12 |
| `duplicate-backend` | 60 | 12 |
| `unknown-backend` | 60 | 12 |
