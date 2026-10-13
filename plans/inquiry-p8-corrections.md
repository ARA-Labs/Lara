# Restore the approved inquiry evaluation

**Status:** Tasks 1–3 are complete; Task 4 remains. Corrective implementation reviewed: engineering review CLEAR by independent agent on 2026-10-12, for code/proof/candidate preparation only. The original P8 run is sealed incomplete. This plan authorizes no new measurement. Researcher approval of the exact corrected protocol, code/input pins and a fresh budget is required before Task 4.

**Tracker:** [Issue #49](https://github.com/ARA-Labs/Lara/issues/49), with P8/P9 remaining in issue #22.

**Goal:** Complete the original 96-document evaluation without dropping the 40-slot workloads, weakening T07's accepted-to-accepted contrast, increasing ceilings or changing frozen inquiry semantics.

The retained attempt is `ara/evidence/inquiry-p8/20261012T225824Z-a904130/`, with a sibling capture-only replay and reproduction receipt. T07 contains duplicate support terms; Lean sensitivity enumerates all declared-slot subsets. The runner discovers oracle disagreement only after capture execution. Preserve that evidence and the original additive freeze at `95f63bf`.

## Task 1: Prove and use sparse Lean sensitivity

Keep `Analysis.minimalSlotSets` as the frozen reference. Add a corpus-independent fast procedure derived from same-history differing rows. Normalize each changed-slot set through the deduplicated slot universe. Deduplicate candidate sets; if an empty changed set exists, return every universe singleton in declaration order. Otherwise retain all inclusion-minimal nonempty candidates and order them exactly as the reference's sublists, using reversed declaration-position lexicographic order.

Prove exact list equality with the frozen reference, including order and duplicate handling. Preserve all differing rows and the existing first-realizer `find?`. Switch runtime sensitivity only through a full result-equality theorem. Add every new theorem to `AxCheck.lean`; remain sorry-free within `propext`, `Classical.choice` and `Quot.sound`, without `Lean.ofReduceBool`.

- [x] Implement candidate normalization, minimality and ordering with named module seams.
- [x] Prove `minimalSlotSetsFast_eq_minimalSlotSets` and complete sensitivity-result equality.
- [x] Verify no flips, differing histories, rejected observations, duplicate identities/changed sets, incomparable minima, nonnumeric declaration order, first realizers and empty-change zero/nonzero-universe cases.
- [x] Build and run required local gates; independent spec and quality review before commit.

No wire, ceiling, legacy golden, corpus, mutation-seed or freeze-tag change is needed. This is substantial local proof/build work; Haskell tests remain conformance evidence.

## Task 2: Stop on semantic discrepancies during execution

After both driver captures and consumer records for a case are attached, call the existing pure scorer before advancing. Keep driver agreement, oracle agreement, protocol validity, consumer acceptance and locality soundness separate. Any failed required predicate seals an incomplete semantic-discrepancy checkpoint and stops before the next case. Preserve successful process records; semantic disagreement is not an infrastructure failure.

- [x] Implement pair-level semantic checkpoints while retaining all current atomic IO/replay guarantees.
- [x] Test two fake drivers returning the same valid but wrong first-case result: exactly two driver and two consumer calls, both captures retained, next-case calls missing, byte-identical nonzero process-free replay.
- [x] Cover one-driver disagreement, protocol/locality failures and interruption between pair scoring and checkpoint publication. Retain semantic-discrepancy details separately if recovery changes the primary stop reason.
- [x] Pass independent spec and quality review; commit without production inquiry calls.

## Task 3: Prepare and independently review corrected inputs

Author a new additive candidate suite outside the original frozen input directory. Keep the 16/16/64 partition, levels, query meanings, control bytes and T07 expectations. In T07's after-policy clone rule `r-s` under fresh `RuleId r-s-new`; only new-attacker uses that rule. Its premise and conclusion stay `seed` and `s`. Existing support terms remain unchanged and the new term is genuinely distinct. Redraw and verify the four-node graph, propagated attacks, defeated status and failed locality before encoding. Apply the corresponding repair to its four source-declaration variants.

- [x] Add an authoring guard for these explicitly ground, annotated support keys; include rule/leaf identifiers, substitutions, nested premises, discharges, holes and assurance, excluding argument/derived claim names. Do not create another source checker.
- [x] Include the old cloned term as a negative guard example and the distinct-rule term as a positive one.
- [x] Author every corrected input/oracle/counter and obtain independent source/graph/row/history/certificate review without production driver outputs as expectations.
- [x] Parameterize and pin candidate suite/audit paths and the input commit in the manifest loader; retain exact validation of the original suite and process-free replay of its archived helper sources.
- [x] Prepare exact code/input hashes and reproduction commands for researcher review; preserve original code/input commitments in the old evidence.

The candidate is not an approved freeze until the researcher approves the justified correction and exact protocol hash. No legacy regeneration or existing freeze-tag bump is proposed.

## Task 4: Review the correction and request a new local budget

Prepare the complete reviewable code, proofs, candidate suite, failure report and protocol amendment before asking for approval. Propose one fresh 96-document, 192-invocation local run with the original 10-second per-driver and 45-minute aggregate ceilings, sequential single-CPU execution and no retries. Pin the approved corrective code and additive input commits before execution. The original failed attempt remains in all reporting; no evidence is replaced.

- [ ] Obtain researcher approval of the exact corrective protocol, code/input pins, data policy and full fresh budget.
- [ ] Freeze the approved additive inputs, finish builds/gates outside measurement, then execute the runner once.
- [ ] Retain every outcome and reproduce deterministic reports from saved captures without driver or consumer calls.
- [ ] Complete the original P8 report and researcher review, update issue #22 and current subject docs, then open the implementation PR.

If the new run is incomplete, stop and retain it. P9 stays separately designed and approved; this correction supplies no live-loop, paid-agent, physical-capture, calibration, causal or scientific-discovery authorization.

## Engineering review

CLEAR for corrective implementation only. The review checked exact ordered-list equality, last-occurrence slot deduplication, declaration-position ordering, immutable reference definitions, source-support identity, separate semantic/process failure judgments and the fresh approval boundary. The candidate path/pin and interruption-diagnosis obligations above are required implementation seams. No new measurement or input freeze is approved by this review.
