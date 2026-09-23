# Yu & Zenker 2020 — Schemes, Critical Questions, and Complete Argument Evaluation

_Reference note on argumentation-scheme evaluation, focused on what it means for Lara's
`claim-support` AST and `undercut`/`rebut` typing. Written 2026-07-21._

> **Provenance flag.** The stable machinery below (schemes, CQs, the three-way premise
> classification, Pollock defeater types, burden of proof) is bedrock Waltonian / Carneades
> argumentation theory and is stated with confidence. Yu & Zenker's *specific* thesis is
> reconstructed from memory and marked as such — fetch the paper to verify exact quotes/claims
> before citing it in the spec.

## The setting

Lives in the **Waltonian tradition** of informal logic. Real arguments rarely fit deductive
templates; they instantiate **argumentation schemes** — stereotyped, *defeasible* inference
patterns (Argument from Expert Opinion, Cause to Effect, Analogy, Sign, Consequences, Popular
Opinion, …). Each scheme ships with **Critical Questions (CQs)** — the standard ways to probe or
attack an instance.

The received picture of *evaluation*: (a) check the instance fits a scheme, (b) check its
premises, (c) run the CQs. Passing all three ≈ presumptively acceptable.

**Yu & Zenker's target question:** does "premises + scheme + CQs" actually enumerate *all* the ways
an argument can fail — i.e. deliver a **complete** evaluation? Reconstructed answer: **not as usually
formulated.** The account must be tightened before "complete evaluation" is even well-defined.

## The load-bearing structure: three component kinds, sorted by burden of proof

The deepest move (Carneades / Gordon–Walton) classifies an argument's components by *how burden of
proof behaves*:

| Component | Default status | When questioned |
|---|---|---|
| **Ordinary premise** | holds only if backed | asking → burden on **proponent** to support |
| **Assumption** (implicit premise) | presumed to hold | asking → burden on **proponent** |
| **Exception** | presumed **not** to hold | asking does nothing; **questioner** must produce evidence it obtains |

This maps directly onto **Pollock's defeater types**:

- Attacking a **premise/assumption** = **rebutting**-style (denies a link in the support).
- Asserting an **exception** = **undercutting** = attacking the *inference* itself, not any stated
  premise.

So a CQ is never "just a question." Each CQ *secretly belongs to one of these three categories*, and
the category fixes who bears the burden when it is raised. **The confusion the paper attacks: CQ
lists are written as flat lists of English questions, hiding these load-bearing structural
differences.**

## Why schemes + CQs don't obviously give completeness

**(a) CQ lists are ad hoc and non-exhaustive.** Walton's own CQ sets differ across publications;
there is no principled generator saying "these and *only* these" are the attacks on a scheme. So
"answer all the CQs" can't guarantee completeness — you'd need to know the list is *closed*.

**(b) The premise/CQ boundary is unstable.** Many CQs re-express as premises ("Is E biased?" ⇔ the
assumption "E is not biased"). If a CQ is really a hidden premise, the scheme's *true* premise set
is larger than stated. But **exception-type** CQs resist this: turning an exception into a premise
*flips the burden of proof*, changing the argument's dialectical meaning. So you **cannot** uniformly
"premise-ify" CQs without distortion.

**(c) Two evaluation dimensions get conflated.** A *logical/semantic* question (are premises
acceptable? is the inference structurally OK?) vs. a *dialectical/procedural* question (whose turn is
it to prove what?). Schemes + CQs blur these; a complete evaluation must say which it is completing.

**Reconstructed proposal:** complete evaluation requires making the scheme's full structure explicit
— ordinary premises, assumptions, *and* an explicit exception set — then sorting every CQ into
exactly one slot. "Run the CQs" then becomes principled: premise/assumption CQs shift burden to the
proponent; exception CQs require the challenger to discharge a burden. **Completeness is relative to
that explicit structure, not to an ad hoc question list.**

## Worked example — Argument from Expert Opinion

> *Premise:* Dr. Smith (climate scientist) asserts sea levels will rise ~1m by 2100.
> *Conclusion:* Sea levels will rise ~1m by 2100.

Sorting the CQs by burden:

- *"Is Dr. Smith an expert in climate science?"* → **assumption**; merely asking obliges the
  proponent to support. (Rebutting-type.)
- *"Is the assertion within her field?"* → **assumption**, same behavior.
- *"Is Dr. Smith biased (e.g. interested funding)?"* → **exception**; asking does not defeat the
  argument — the challenger must *show* the bias. (Undercutting-type: doesn't rebut the conclusion,
  doesn't deny she's an expert; it severs the inferential warrant.)

Flattening that last CQ into "just another premise" is a category error — it would silently flip the
burden of proof.

## Why this matters for Lara

1. **`undercut` vs `rebut` typing is not cosmetic** — it *is* the exception-vs-premise distinction,
   and getting it right is a *precondition* for claiming evaluation completeness. Retyping C05 as
   undercut is this methodology in miniature.
2. **"Complete argument evaluation" is a spec target.** To be complete in Yu & Zenker's sense the
   AST + evaluation need (i) an explicit **exception set** per support relation, not just premises,
   and (ii) **burden-of-proof semantics** on attack edges (who must discharge what). A flat "attack"
   edge is under-specified.
3. **Rejection-class negatives** map onto their concern that CQ lists aren't closed — characterizing
   the space of legitimate rejections is exactly the generator the informal tradition lacks.

## Open questions to hold onto

- **Is exhaustive completeness achievable?** Defeasible reasoning is open-textured; new exceptions
  arise from world knowledge. "Completeness relative to an explicit structure" may be the best
  available — decide which Lara claims.
- **The premise/exception line is itself contestable** in real cases (bias can be framed either
  way), which risks reintroducing the instability the paper wants to remove.
- **Formalization tax:** making every scheme fully explicit (premises + assumptions + exceptions +
  burden rules) is heavy; the appeal of Walton's schemes was lightweight usability.

## To verify against the source

- [ ] Exact statement of Yu & Zenker's completeness thesis and their proposed fix.
- [ ] Full citation (venue, year, page) — confirm 2020.
- [ ] Whether they explicitly invoke Pollock's undercut/rebut vocabulary or only Carneades'.
