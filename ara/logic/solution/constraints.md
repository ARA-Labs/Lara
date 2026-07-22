# Constraints, assumptions, limitations

_Source: `docs/spec.md` §1, §11; `docs/comparison-rit-lara.md` §6–8; `docs/strict-backend-decision.md`
§7. What LARA does and does not guarantee, stated plainly (the "state the trusted boundary bluntly"
lesson from EG-VAR, `docs/prior-art-lessons.md`)._

## Boundary conditions

- **Structural validity only.** Checker acceptance means the argument is well-typed and undefeated
  relative to the selected policy, backend theories, and admitted leaves — NOT that any claim is
  empirically true. "compiles ≠ claim true; compiles = the argument is well-typed and undefeated, given
  its evidence and the chosen policy."
- **Policy-relative completeness.** "Complete" means every premise and critical question of an
  instantiated scheme is discharged or surfaced as a hole — not mechanical completeness of a scientific
  argument (which is undecidable from a finite artifact without a closed-world assumption).
- **v0.1 fragment.** Support-level propositions are ground first-order atoms; grounded semantics only;
  Path B consistency (strict chains may only target uncontested claims); no AC/symmetric predicates, no
  binders in `nf`. Each is a documented flip criterion, not a permanent limit.
- **No tactic DSL, IDE, package manager, or standard library** for the initial contribution.

## Assumptions (the three-way conditional guarantee)

The end-to-end guarantee is conditional on three unchecked things:

1. **Leaf truth (soundness).** Evidence atoms are untrusted hypotheses; provenance tags and admission
   gate them, but the checker never proves them.
2. **NL→proposition faithfulness (the translation gap).** That `c.formal` faithfully renders `c.nl`.
   No checker can verify this; it is the single most load-bearing unchecked step, human-signed and
   evaluated on the semantic-faithfulness axis (spec §11).
3. **Policy faithfulness.** That a defeasible scheme (and its critical questions) is a correct account
   of what supports the claim. `Π` is a trusted input; policy quality is an evaluated axis, not a
   proven property. "Your checker is only as good as its policy" is the rebuttal-bait — the answer is
   curated-from-methodology-literature, versioned, corpus-validated.

## Known limitations

- **The hard problem is relocated, not removed.** LARA's exposure is not dishonest framing but a
  relocated hard problem: the epistemic content moves into `Π` (trusted, unchecked) and the leaves.
- **Curry–Howard covers adapters, not LARA as a whole.** The clean "well-typed proof term ⟹ valid
  derivation" story applies to proof-term adapters (spec §5). The defeasible layer is
  argumentation-framework defeat, which is not a Curry–Howard phenomenon — a valid argument can be
  retracted by a dead end. The honest framing is a typed argument checker with pluggable strict
  adapters, not an end-to-end Curry–Howard proof system.
- **Realization is not a lowering guarantee.** Artemov's `S4 ⊢ F ⟹ LP ⊢ Fʳ` is theorem-to-realization;
  it says nothing about NL→formal faithfulness (the pivot, trace N05). LP realization is
  optional-adapter metatheory, never the guarantee behind lowering.
- **Two definitional points are open** (must close before M1 freeze): the hole-vs-complete-alternative
  status case (spec §8), and `contested`-SCC provenance reporting (review §6).
- **Result 6 is currently unprovable as written** — no independent direct source semantics exists to
  preserve (see `mechanization.md` §5).
- **Most of the checker is unimplemented.** Only `Lara.Prop` (`nf`/`≡`) is built and tested; the strict
  registry, ND adapter, policy/support-term/attack/compile/grounded layers, JSON codec, parser, and the
  Python elaborator are spec-only. The existing LP code is a non-conforming adapter seed.
- **Benchmarking is out of scope for the first submission** — which raises the weight on metatheory +
  worked examples, so the differentiator (E3) and the rejection-class conformance must be airtight.

## What is out of scope by design

- A graded/probabilistic core (the kernel stays boolean; graded confidence lives in the judge as
  metadata).
- Provenance-as-attack (low-trust provenance supports an admission policy and audit report; it does not
  logically rebut or undercut an argument).
- Model-checker behavioral leaves (TL-1) — optional, strictly outside the kernel, gated by corpus
  open question §8 #7.

## Corpus-derived pipeline constraints (M0, 2026-07-22 — grounds: C16, E09)

- **Attack candidates come from the whole trace.** The elaborator's attack walk must cover
  experiment nodes and score-filtered runs, not only `dead_end` nodes — two artifacts held their
  strongest counter-evidence outside dead ends (fix_embedding C12, triton_cumsum C09).
- **Unmet mandatory CQs are holes, not defeaters.** 39% of mandatory critical questions in the
  corpus are unmet; treating them as attacks would spuriously defeat nearly every claim.
- **Dead ends can support.** A `dead_end` node can be a claim's primary *evidence*
  (restricted_mlm C14); the lowering map needs a support-from-dead-end path, not only attack typing.
- **Result-cell conflicts need a decision.** Conflicting duplicate reports of one result cell
  (figure vs text, bridging-data-gaps C05) are neither an attack nor a provenance grade; spec §7/§8
  must say what the leaf layer does with them.
- **Rebut/undermine test coverage is authored, not mined** (decision N29): the corpus is polished,
  peer-reviewed top-venue work; adversarial reports/mutations against corpus claims are written by
  us at language-testing time, extending the rejection-class negative-suite discipline to the
  defeat layer.
