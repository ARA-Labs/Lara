# Generated mutation suite (M5 tracker #48, T1)

GENERATED — do not edit. Regenerate with:

    cabal exec -- runghc scripts/gen-mutants.hs

Every file is derived from the committed worked-example anchors
(`examples/<NAME>/example.core.sexp`, bases: A B E1 E2 E3 E4 E5 S1)
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

Total mutants: 358

| expected outcome | mutants |
| --- | --- |
| `accept-all-contested` | 4 |
| `accept-contested` | 9 |
| `accept-defeated` | 18 |
| `accept-gap` | 9 |
| `accept-justified` | 9 |
| `codec-reject` | 45 |
| `reject-IncompleteArgument` | 18 |
| `reject-R1` | 44 |
| `reject-R10` | 11 |
| `reject-R11` | 19 |
| `reject-R12` | 20 |
| `reject-R13` | 41 |
| `reject-R3` | 19 |
| `reject-R4` | 18 |
| `reject-R5` | 18 |
| `reject-R6` | 18 |
| `reject-R7` | 19 |
| `reject-R9` | 19 |

| mutation family | mutants |
| --- | --- |
| `accept-verdict` | 45 |
| `bad-attack-targets` | 30 |
| `certificate-tampering` | 60 |
| `codec-corruption` | 45 |
| `cycles` | 4 |
| `data-integrity` | 19 |
| `hidden-policy-extension` | 39 |
| `open-obligations` | 54 |
| `undeclared-leaves` | 25 |
| `wrong-formulas` | 37 |

## Corpus sweep (uniform derived-applicability, B = 12)

Per rejection operator over the corpus units: how many bases carry ≥1
site (applicable) and how many were selected (all when ≤ B, else B
picked by the operator-keyed stream). Cert operators find no corpus
site (corpus units carry no strict certificates), recorded as 0/0.

| corpus operator | applicable bases | selected |
| --- | --- | --- |
| `undeclared-leaf` | 12 | 12 |
| `hidden-rule` | 12 | 12 |
| `hidden-contrary` | 60 | 12 |
| `wrong-subst-domain` | 12 | 12 |
| `wrong-premise` | 12 | 12 |
| `open-obligation` | 12 | 12 |
| `hole-obligation` | 12 | 12 |
| `wrong-discharge` | 12 | 12 |
| `trusted-assurance` | 12 | 12 |
| `cert-theory-swap` | 0 | 0 |
| `cert-payload-tamper` | 0 | 0 |
| `bad-attack-position` | 3 | 3 |
| `unlicensed-attack` | 12 | 12 |
| `group-conflict` | 55 | 12 |
| `duplicate-backend` | 60 | 12 |
| `unknown-backend` | 60 | 12 |
