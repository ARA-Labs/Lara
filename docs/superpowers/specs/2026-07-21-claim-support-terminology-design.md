# Claim-Support Terminology

Status: approved on 2026-07-21.

## Decision

Use **claim-support calculus** as the public and technical name for LARA's
source calculus. This replaces "warrant calculus," whose legal connotation is
distracting for a broad research audience.

"Support" is always policy-relative and defeasible. A checked support term
does not establish that its conclusion is empirically true.

## Vocabulary

| Previous term | Replacement |
| --- | --- |
| warrant calculus | claim-support calculus |
| warrant certificate | claim-support certificate |
| warrant term | support term |
| warrant rule | inference scheme |
| warrant policy | claim-support policy |
| warrant graph | claim-support graph |
| "`w` warrants `p`" | "`w` supports `p`" |

Use the shorter "support term" rather than "claim-support term" for recursive
objects. Use "inference scheme" for both strict and defeasible policy entries;
the scheme's declared mode determines how an instance is checked.

The compiled technical target remains a Dung argumentation framework. In
broad-facing material, "claim-support graph" names the checked graph before
and during status explanation.

## Terms That Stay

Keep these established terms:

- evidence leaf;
- strict and defeasible;
- critical question and obligation;
- rebut, undercut, and undermine;
- attack;
- grounded semantics;
- `justified`, `gap`, `defeated`, and `contested`.

Retain "warrant" only when discussing or quoting prior argumentation theory,
or when explaining the terminology migration.

## Formal Reading

The judgment keeps its current structure:

```text
Sigma; Pi; Gamma; R |- w : supports(p) ▷ O
```

Read it as:

> Under signature `Sigma`, claim-support policy `Pi`, admitted leaves `Gamma`,
> and backend registry `R`, support term `w` supports proposition `p` with open
> obligations `O`.

This is a terminology change, not a change to checking, compilation, attack
typing, grounded evaluation, or claim-status aggregation.

## Migration Scope

Apply the terminology consistently to:

1. the README, proposal, specification, engineering plan, and decision notes;
2. future Haskell modules and types, such as `Lara.SupportTerm`;
3. presentation syntax, JSON field names, diagnostics, and report labels before
   the v0.1 wire format freezes;
4. paper prose and evaluation materials.

Do not mechanically replace uses inside citations, titles, historical
descriptions, or discussions of established warrant theory.

## Acceptance Criteria

- Public descriptions introduce LARA as a claim-support certificate language.
- Every use of "support" states or inherits the policy-relative, defeasible
  reading.
- Source and wire terminology agree before v0.1 freezes.
- Remaining uses of "warrant" are intentional references to prior theory or
  migration history.
- Existing formal behavior and test expectations do not change.
