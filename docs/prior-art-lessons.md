# Prior-art lessons: what to borrow, what to avoid

_Firsthand reads of the closest prior systems, focused on concrete design/eval lessons for Lara
rather than positioning (positioning lives in `novelty-and-related-work.md`). Written 2026-07-21._

_Currently covered: EG-VAR (read to answer "what does a monotonic,
attestation-based verifier of empirical claims get right and where does it
relocate trust?"), followed by cross-system takeaways. The delta table over
the full neighbor set is in `novelty-and-related-work.md`._

## EG-VAR (Ren 2026, ICML TAIGR workshop, arXiv:2607.12650)

### What it is (firsthand)

A four-layer stack for verified empirical claims: **L1** deterministic tool queries → **L2** audited
per-source "lifts" from storage to world facts → a **Lean 4 kernel** that mints `Verified` claims →
a **solver LLM** that proposes a proof the kernel checks. The load-bearing mechanism: `mkVerified`,
the sole constructor of `Evidence Verified w`, *requires* an `Attested_T` token emitted by the
runtime, so every verified output structurally descends from a real tool call. The answer is the
witness of a dependent-sum (Σ-type) goal (Curry–Howard). Two safety theorems: **3.1** no unsupported
Verified outputs (every observation-leaf axiom traces to a recorded tool execution), **3.2** no
deductive errors (everything type-checks under the declared axiom set). Non-verifiable cases return
an honest **Abstain** with a replayable audit trail.

### Honest assessment

- **Venue/scale.** ICML 2026 TAIGR **workshop**, single author, v1. Eval is n=120 on one TableBench
  numerical-reasoning subset, single-table only.
- **The title overclaims.** "Eliminating LLM hallucination" is not what the system does. Its own
  App. M.1(ii): tools, per-source lifts, and the L1 adapter are **trusted, not type-checked
  end-to-end**, and "a semantically wrong audited lift can certify a wrong formalized claim." It
  rules out unsupported claims *between tool and output*; it does not remove curator error. Trust is
  **relocated to the lift**, not eliminated.
- **The hard part still fails.** Tier 1 (120/120) uses fixture-committed gold typed goals that
  **bypass the NL→Lean formalizer**. Only Tier 2 runs the formalizer end-to-end, where residual
  semantic-formalization error is 3.3% (Sonnet) / 1.7% (Opus). The proposed 3-blind-formalizer
  consensus is "implemented but not evaluated."
- **It is purely monotonic.** No defeasible reasoning, no defeat, no argumentation, no
  critical-question completeness. A recorded dead end cannot retract a prior conclusion.

### What to borrow

1. **The `mkVerified`-requires-`Attested_T` constructor pattern → Lara TL-1 certified leaves.**
   Making the *constructor* of an admitted fact require a runtime witness token is a clean, mechanized
   realization of what spec §4.3 leaf admission wants for a `certified` leaf (provenance
   `checker(name, version)` + replayable reference). EG-VAR shows the Lean encoding. Directly useful
   when/if the optional TL-1 track is built; borrow the "sole constructor needs a witness" shape.
2. **The Tier-1 / Tier-2 eval split corroborates Lara's four axes.** EG-VAR measures the *kernel*
   safety property in isolation (Tier 1, formalizer bypassed with gold goals), then measures the
   *formalizer* separately (Tier 2). That is exactly Lara's Axis (a) (metatheory/conformance,
   LLM-independent) vs. Axis (b) (semantic faithfulness) separation. Independent evidence the split is right, and a concrete
   template: report the checker guarantee under ideal formalization *and* the end-to-end residual
   separately; never launder one through the other.
3. **State the trusted-lift caveat plainly, as they do.** M.1(ii) names the trusted boundary in a
   limitations section instead of burying it. Lara's leaf-interface caveat (spec §3.3, §11) should be
   stated with the same bluntness — it is the honest move and it pre-empts the reviewer.

### What to avoid

- **Do not let the title outrun the guarantee.** EG-VAR's "eliminating hallucination" vs. its own
  M.1(ii) is the cautionary case. Lara's guarantee is conditional and policy-relative (spec §1); say
  so in the title/abstract framing, not only in §11.
- **Do not evaluate only under ideal formalization.** A 120/120 that bypasses the formalizer is a
  kernel result, not an end-to-end result. Lara's Axis (b) must run the untrusted producer for real.
- **Do not claim novelty EG-VAR already occupies.** Tool-attestation + Lean kernel + honest
  abstention for *monotonic* empirical claims is theirs. Lara's ground is the **defeasible +
  argumentation + policy-completeness** layer they explicitly lack.

## Reusable takeaways (cross-system)

- **Attested-constructor pattern** (EG-VAR) — a leaf/fact type whose only constructor demands a
  runtime witness. Map onto spec §4.3 `certified` admission and TL-1.
- **Isolate the trusted-formalization residual** (EG-VAR Tier split) — always report the checker
  property separately from the NL→formal faithfulness rate. Confirms Lara Axis (a)/(b).
- **Positional-identity support** (AIF, Micropublications) — support is an out-edge landing on the
  claim node, not an entailment query. Already adopted in spec §3.1; the lesson is to *keep* it and
  resist entailment creep into the TCB.

_Add further firsthand reads (Pandžić, Micropublications) here as they are done, same format:
mechanism → honest assessment → borrow → avoid._
