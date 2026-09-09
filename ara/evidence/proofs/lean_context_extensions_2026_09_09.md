# Lean context extensions — 2026-09-09

The user requested implementation in issue order and separate PRs. All PRs are open and stacked in that order; none was merged by this session.

## #281: Named checker soundness facts

checkUnit_sound now returns CheckUnitSound with named fields; all consumers migrated; checker and propositions unchanged.

Commit `aa5168d`; [PR #296](https://github.com/ARA-Labs/lara/pull/296). Trace `N277002`.

Validation output copied from the completed local gate logs:

```text

Build completed successfully (160 jobs).

AxCheck coverage passed (2675 declarations).

Axiom audit passed.

Lean citations: PASS (404 citations, 36 allowlisted)

ARA source spans: PASS (62 quotations)

```

## #197: Enumeration conflict-freedom removes incidental Nodup

Enumeration-based exclusivity and concrete instance discharges require no Nodup; spec-based theorem signatures remain as wrappers.

Commit `5f38b2f`; [PR #297](https://github.com/ARA-Labs/lara/pull/297). Trace `N277003`.

Validation output copied from the completed local gate logs:

```text

Build completed successfully (160 jobs).

AxCheck coverage passed (2683 declarations).

Axiom audit passed.

Lean citations: PASS (404 citations, 36 allowlisted)

ARA source spans: PASS (62 quotations)

```

## #198: Central semantics registry with declaration coverage

The table consumes a central registry; an elaborated-environment audit rejects unregistered named closed repository semantics, including unimported modules. Parameterized families and local values remain outside the finite inventory.

Commit `d1d0e73`; [PR #298](https://github.com/ARA-Labs/lara/pull/298). Trace `N277004`.

Validation output copied from the completed local gate logs:

```text

Build completed successfully (161 jobs).

AxCheck coverage passed (2684 declarations).

Axiom audit passed.

Lean citations: PASS (404 citations, 36 allowlisted)

ARA source spans: PASS (62 quotations)

Semantics registry audit passed (117 modules).
semantics goldens: PASS

----------------------------------------------------------------------
Ran 9 tests in 95.723s

OK

```

## #268: Refute unrestricted transfer of grounded contextual equivalence

A proof over every context equates grounded observations for fragments differing only in export; an adequate positional singleton selector distinguishes them in an accepted context. Standard-semantics and identical-export restrictions are not resolved by this witness.

Commit `8bc580f`; [PR #299](https://github.com/ARA-Labs/lara/pull/299). Trace `N277005`.

Validation output copied from the completed local gate logs:

```text

Build completed successfully (162 jobs).

AxCheck coverage passed (2691 declarations).

Axiom audit passed.

Lean citations: PASS (404 citations, 36 allowlisted)

ARA source spans: PASS (62 quotations)

Semantics registry audit passed (118 modules).

```

## #217: Typed CQ holes and contextual substitution

Independent template typing and equivalent typed fillings derive core support; erasure derives open source support. Instantiated arguments and attack endpoints enter the old checked linker. Conservative embedding, composition and backend transport are proved; fixing contexts includes filling certificates. Nested fixtures include a typed attack, errors and positive transport applications.

Commit `9ba73dd`; [PR #300](https://github.com/ARA-Labs/lara/pull/300). Trace `N277006`.

Validation output copied from the completed local gate logs:

```text

Build completed successfully (169 jobs).

AxCheck coverage passed (2810 declarations).

Axiom audit passed.

Lean citations: PASS (400 citations, 36 allowlisted)

ARA source spans: PASS (62 quotations)

Semantics registry audit passed (125 modules).

```

## Proof scope

`Lara.Examples.ContextualSeparation.grounded_ctxEquiv` supplies the universal-context premise; `singleton_not_ctxEquivSem` supplies the accepted distinguishing context. The family `singletonSem` satisfies the existing adequacy interface. This is not a claim of separation at a standard non-grounded semantics.

`Lara.Context.Holes.instantiate_hasSupport` derives final support from independent `HasTemplate` and `FillingTyped` premises. `eraseOpen_hasSupport` reconstructs an actual open core derivation. Post-substitution attack coverage remains explicit; substitution is not assumed injective. Filling values are core terms, while named holes can nest in templates. Full abstraction remains outside this result.

The positive nested-hole transport fixtures do not move certificates; the separate independently typed certified-filling witness proves that fixing the old frame does not imply fixing a hole context.

Independent reviews found no remaining soundness issues. A missing AxCheck entry and a missing positive transport application were identified and corrected before final verification.
