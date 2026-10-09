# D6: a checked statistical method is not empirical truth

Lara checks two different things about a research artifact. The `.lara` checker
asks whether a claim's declared support survives every declared attack. Belief
Hoare Logic (BHL) asks whether the statistical procedure behind the claim is
valid under explicit assumptions. This demo separates those questions with
three checked witnesses, all in [lean/Lara/Examples/](../../lean/Lara/Examples/).

Every result quoted here is a named Lean declaration, and
`cd lean && lake exe bhl-examples` replays them. The demo adds no `.lara`
syntax and no CLI command.

## What the three parts of a method judgment are

BHL splits one informal question, "is this method sound here", into three
judgments with different evidence and different conclusions.

| Judgment | What it needs | What it concludes |
| --- | --- | --- |
| Conditional method validity | A checked derivation over the exact model and program | Every terminating modeled run from a precondition-satisfying world satisfies the postcondition |
| Modeled application | Conditional validity, actual precondition satisfaction in the initial world, and the exact execution | The final modeled world satisfies the postcondition |
| Artifact warrant | Selected support and every named applicability dependency surviving admission, checking, grounded justification and blocking | Those supports stay eligible. It says nothing about the assumptions they carry |

The distinction matters because only the middle judgment depends on the world
the experiment actually ran in. The [theory record](../theory-bhl.md) states
the contracts; the declarations below are their witnesses.

## Episode 1: support for an assumption is not the assumption

`false_precondition_conditional_success` checks a conditional method, and
`false_precondition_applied_failure` shows the same method applied to a world
whose precondition is false, rejected with `.falsePrecondition`.
`false_precondition_no_modeled_application` proves no modeled application
exists for that binding.

The stronger negative is `supported_applicability_false_precondition`: an
argument is `published .justified` in the ordinary checker, and the
precondition of the method it serves is still false. Support does not
discharge a mathematical premise. `supported_applicability_no_knowledge`
extends the same case to BHL knowledge itself: admission of the initial world
is required before the truth law can be used, and support supplies neither.

`belief_without_truth_boundary` closes the loop on the epistemic side.
Statistical belief holds at a world where the alternative does not. Belief is
a statement about the procedure and its null model, not about which hypothesis
is true.

## Episode 2: withdrawing evidence moves warrant, not the theorem

`dependency_tighten` applies a real `tighten` update to an accepted source
whose named applicability argument and selected argument are distinct raw
occurrences. Three facts follow, each checked: the named dependency leaves the
kept arguments and gets no gamma context (`dependency_named_pruned`), it has
no support at any conclusion in the target (`dependency_target_no_support`),
and the target certificate fails with `.missingSupport`
(`dependency_bridge_target_failure`), while the source certificate succeeds
(`dependency_bridge_source_success`).

The mathematical side is untouched: `dependency_conditional_unchanged` proves
the conditional method holds before and after. Loss of warrant and loss of
validity are different events.

An independent argument using a different leaf survives in the same target
(`dependency_alternative_support`, `dependency_alternative_eligible`), which is
why the selected claim stays justified. Quarantine removes one dependency, not
the claim.

The safe direction has its own conditions. `harmless_source_distinct` shows
that adding a fresh unrelated leaf really does change the source, and
`harmless_stale_certificate` shows the old certificate is refused with
`.staleSnapshot`. Warrant survives only through explicit rebinding, where
`harmless_rebound_warrant` derives the target warrant from the declared
transport conditions and `harmless_rebind_success` rechecks the fresh
certificate. Rebind conditions are stated hypotheses, not a promise that every
harmless edit is free.

## Episode 3: one reported result, two compatible histories

`Lara.Examples.BHLPartialRecord` builds two complete reference executions in the
same admitted binary model. The reported-only run executes one test. The
second run executes an earlier unreported test and then the same final one, so
its complete ledger has cardinality two
(`different_full_ledgers`).

Both runs produce exactly the same nonempty submitted record, target, test
identity, datum and value `1/4`, which `record_compatible` checks for both
completions. Their method conclusions differ: `reported_conclusion` is true
for the short run and `omitted_test_conclusion` is false for the long one,
with `checkConclusion_correct` tying each finite evaluation to independent
satisfaction in the corresponding complete history.

`record_does_not_determine_conclusion` states the consequence: no function
from this submitted record to a Boolean can agree with the method conclusion
in every compatible complete history. The theorem is specific to this witness.
It does not say that partial records are useless, and it is not a general
calculus of compatible completions.

## What this demo does not show

Physical sampling as modeled, interpretation fidelity of the natural-language
claim, completeness of an external log, and the adequacy of the null model for
a real population all stay outside the checked model. Those are stated
obligations, not hidden assumptions. The
[reference audit](../theory-bhl.md#which-discrepancies-require-corrections)
records the corrections to published BHL statements. The same theory record's
[comparison](../theory-bhl.md#which-assumptions-change-and-what-novelty-is-established)
separates inherited results from Lara-specific composition.
