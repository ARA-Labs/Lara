# Production quarantine non-promotion

## Result

`Lara.BlockedProgram.checked_production_justified_nonpromotion_of_not_blocked`
closes the production bridge for duplicate-report quarantine. It instantiates the
abstract declared-index non-promotion theorem with the exact compact AF built by
the shipped driver.

The bridge has four explicit parts:

1. `retainedView` pairs every declared argument with its original index before
   filtering, so retained arguments and the index embedding cannot drift.
2. `selectAligned` filters raw attack declarations and their resolved attacks in
   lockstep. The exact attack list passed to `checkUnit` is therefore a proved
   sublist of the declared resolved attacks.
3. `compile_checkedAF_embedding` embeds `Compile.checkedAF` into the declared-index
   AF and proves agreement of attacks, direct labels, and justified status.
4. The checker-instantiated theorem obtains the exact argument and attack
   equalities from `Check.Unit.checkUnit_sound`, derives the attack-sublist fact
   from the raw/resolved aligned filter, derives the unblocked-support premise
   from absence in the production `blockedQueries`, and applies
   `justified_nonpromotion` after lifting the compact claim.

This deliberately proves implication, not status equality. The latter needs the
equal-support premise exposed by `statusC_agree` and is not available after a
proper quarantine deletion.

## Verification (2026-08-05)

- `cabal test`: PASS.
- `cd lean && lake build`: PASS (56 jobs; only pre-existing warnings in
  `Lara/Examples.lean`).
- `cd lean && lake env lean AxCheck.lean | ../scripts/check-axioms.sh`: PASS.
- `bash scripts/differential.sh`: positive `436/436`, negative `54/54`.

The Haskell and Lean production paths now use the same identity discipline:
support use decides argument retention, surviving raw endpoint IDs decide attack
retention, and structural alignment selects the already-resolved attack values
used by the checker and proof.
