# Blinded Binding-Audit Results and Deterministic Reporting

Status: approved in conversation on 2026-08-09. **Implementation state
(2026-08-19): the pipeline landed in PR #96; the audit itself has not run.**
Every artifact this document specifies under `measurements/binding-audit/`
other than `worklist.tsv` — `results.tsv`, `object-results.tsv`,
`summary.json`, `README.md` — is still unwritten, because no second-author
judgments have been collected. Tracked as issue #121.

## Goal

Complete issue #87 Steps 1–3 without weakening its blinding boundary. A second
author audits all 38 load-bearing leaf bindings, the one load-bearing strict
step, and the three validated typed attacks. Human judgments remain sealed and
status-free. A separate deterministic analyzer validates those judgments, joins
checker verdicts only after the audit is complete, computes the paper-facing
counts, and renders a reproducible summary.

The audit asks whether each formal object faithfully represents its associated
prose or source rationale. It does not judge whether the scientific claim is
true, whether the experiment is well designed, or whether the checker verdict
is correct.

## Non-goals

- Do not change any classification while joining checker statuses or preparing
  the report.
- Do not expose checker verdicts in an audit input.
- Do not edit the frozen corpus, fixtures, `measurements/frozen/`, checker,
  Lean development, wire format, replay bundles, or freeze tag.
- Do not repair an unfaithful or underdetermined binding in this change.
- Do not sample the 38 leaves; the audit is exhaustive.
- Do not add a second interpretation of attack endpoints. Reuse raw source
  attack IDs aligned with the checked semantic attacks.
- Do not hand-compute paper numbers.

## Artifacts

### Existing generated input

`measurements/binding-audit/worklist.tsv` remains byte-unchanged. Its 38 rows
are the complete leaf denominator, in manifest/dependency order, with no
checker status. The existing freshness property continues to own this file.

### Sealed leaf judgments

Add `measurements/binding-audit/results.tsv` with this fixed schema:

```text
unit\tleaf_id\tclassification\tjustification\tdivergence_note
```

The `(unit, leaf_id)` sequence must exactly equal `worklist.tsv`. The human
columns obey these rules:

- `classification` is exactly `faithful`, `unfaithful`, or `underdetermined`;
- `justification` is nonempty for every row;
- `divergence_note` contains a substantive note when the classification is
  `unfaithful`, and is exactly `-` otherwise;
- TSV cells use the same backslash escape contract as the worklist.

The file contains no verdict or derived cross-tab column. Once the second
author completes it, it is the sealed leaf-audit record and the analyzer never
rewrites it.

### Sealed strict-step and attack judgments

Add `measurements/binding-audit/object-results.tsv` with four rows:

```text
subject_id\tunit\tsubject_type\tformal_object\tprose_context\trefs\tclassification\tjustification\tdivergence_note
```

The denominator is fixed:

- one `strict-step` subject for `adaptive-pruning.C04`'s checked
  `rational_drop_recheck` step;
- three `typed-attack` subjects, one for each checked undercut.

`subject_id`, unit, type, formal object, prose context, order, and refs are
generated from the same loaded corpus records used by claim-support reporting.
Typed attacks retain raw `ArgId` endpoints aligned with their checked semantic
attacks; term equality is never used as identity. The second author fills only
classification, justification, and divergence note. The same enum and
nonempty-field rules as `results.tsv` apply.

### Generated summary

Add `measurements/binding-audit/summary.json`. It is generated after both sealed
judgment files exist and contains:

- leaf totals: audited, faithful, unfaithful, underdetermined;
- the same counts split by `attested` and `observed`;
- the same counts over the paper-anchored subset;
- a checker-status cross-tab, including the number of unfaithful leaf bindings
  under units whose requested claim is `justified`;
- separate classification counts for the strict step and the three typed
  attacks;
- the exact corpus/freeze identity and audit input digests needed to identify
  the analyzed snapshot.

The status cross-tab is by the requested claim status already carried by each
manifest unit. It does not invent a status for an unqueried intermediate claim.

### Method record

Add `measurements/binding-audit/README.md`. It records the auditor, audit date,
classification definitions, allowed reference material, blinding procedure,
sealing point, analyzer command, and a warning that the audit assesses binding
faithfulness rather than scientific truth. It cites `summary.json` for all
numbers instead of duplicating hand-calculated totals.

## Architecture

### Pure library

Add `Lara.BindingAudit` to own:

- closed `AuditClassification` and audit-subject types;
- escaped-TSV parsing and rendering for both result schemas;
- exact worklist/result key validation;
- deterministic derivation of the four non-leaf audit subjects;
- post-seal joins against manifest-driven `UnitRecord`s;
- aggregate count and cross-tab calculation;
- canonical `summary.json` rendering.

`UnitRecord` currently retains only strict-step and typed-attack counts. Extend
the reporting projection with the checked strict-step subject and raw attacks
aligned to the semantic attacks, then consume those values here. Do not modify
the checker, identify attacks by semantic-term equality, or re-resolve attacks
after filtering.

### Command

Add `scripts/binding-audit.hs` with three explicit modes:

- `prepare <output-dir>` creates a detached, status-free review packet
  containing the exact worklist, a keyed leaf-results template, and the
  generated four-row object-results template. It refuses an existing output
  directory and never writes under the repository's committed
  `measurements/binding-audit/` directory.
- `validate <packet-dir>` parses and structurally validates a completed packet
  against the generated leaf and object denominators without reading,
  inspecting, joining, or emitting `urStatuses`. It writes nothing. This mode
  runs before the human files are sealed in a commit.
- `summarize` reads the unchanged worklist and both sealed committed result
  files, repeats structural validation, then joins requested-claim statuses,
  forces the complete summary rendering, and atomically replaces only
  `summary.json`.

All modes exit nonzero with contextual `binding-audit:` diagnostics. `prepare`
and `validate` never expose or inspect a checker status. `summarize` never
writes the worklist or either human result file. The existing
`claim-support.hs` command remains unchanged.

## Human Audit Protocol

### Leaf pass

The second author receives the status-free `worklist.tsv` and the documented
lowering conventions. For each row, they compare `formal_target` with
`claim_nl` and record one classification plus one-line justification. They may
consult the cited annotation and lowering rationale, but must not inspect
`expected.json`, aggregate status outputs, or the expected-verdict footer in a
unit before sealing the classifications.

`attested` and `observed` retain their distinct meanings. The auditor judges the
claim each kind purports to encode rather than holding an attestation to the bar
of an observed measurement. The documented Family-10 canonical numeral spelling
is not itself an unfaithful binding.

### Non-leaf pass

The same auditor then judges the generated strict-step and typed-attack
subjects. For the strict step, the question is whether the instantiated checked
rule/certificate assertion matches the associated arithmetic prose. For each
attack, the question is whether the cited source rationale supports the typed
undercut relation against the named target; the task does not ask whether the
attacking evidence is scientifically true.

### Seal and join

The audit is sealed when `results.tsv` and `object-results.tsv` are complete and
committed. Only then may the analyzer load checker statuses and produce
`summary.json`. A later correction to a human judgment requires an explicit
follow-up commit that states the reason; regeneration alone never changes a
judgment.

## Validation and Failure Handling

The analyzer rejects before writing when:

- either result file is missing or malformed;
- a worklist or object key is missing, duplicated, unknown, or out of order;
- a copied generated field differs from the current deterministic projection;
- a classification is outside the closed three-value vocabulary;
- a justification is empty;
- an unfaithful row lacks a divergence note;
- a faithful or underdetermined row carries anything other than the `-`
  divergence sentinel;
- a corpus/worklist/results identity or digest differs;
- a unit has zero or multiple requested-claim statuses;
- the four non-leaf subjects are not exactly one strict step and three typed
  attacks.

All pure output is forced before the atomic summary replacement. A failed run
leaves the prior complete `summary.json` in place and never modifies human
judgments.

## Testing

Add focused tests that defend these observable contracts:

- exact 38-row leaf key/order match;
- exact four-object identity/order match;
- all accepted classification values and every malformed-value rejection;
- missing, duplicate, unknown, and reordered rows;
- escaped cell round trips and malformed escape rejection;
- justification and divergence-note invariants;
- raw attack endpoint alignment, including constructors whose semantic terms
  could compare equal;
- requested-claim status join and the justified/unfaithful cross-tab;
- kind and paper-anchor splits;
- exact deterministic `summary.json` bytes;
- fresh write, overwrite, and failure-preserves-old-summary behavior;
- committed summary freshness after the human files are sealed.

The final repository gate runs the Haskell build/tests, repeats all three
`binding-audit.hs` modes to prove packet validation and summary determinism,
then runs the Lean build and axiom audit, differential, replay/tamper,
authenticity/freshness, formatting, and clean-tree checks. The
external paper must compile, and each reported number must match
`summary.json`.

## Delivery Sequence

1. Implement types, parsers, validation, four-object projection, all three
   command modes, and tests without committing incomplete human result files.
2. Run `prepare` into a detached directory, verify the packet, and hand it to
   the second author.
3. Receive the completed packet, run status-free `validate`, and commit the 38
   leaf plus four non-leaf judgments unchanged.
4. Run `summarize`; commit `summary.json` and write the method README.
5. Update the Overleaf evaluation text and `sec:leaves` cross-reference from the
   generated summary.
6. Run the full repository and paper gates from clean trees.

The human handoff is a hard checkpoint. Steps 3–6 cannot be represented as
complete until the second author supplies the actual judgments.
