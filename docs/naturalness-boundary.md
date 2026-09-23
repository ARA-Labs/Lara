# Naturalness boundary

_Status: settled for language v0.1. Recorded 2026-08-25._

_This note is **policy only**. It authorizes no CNL experiment, no producer code,
and no error-message rewrite. It exists so that ease-of-use work cites a fixed
boundary instead of re-deciding "how natural should this be?" once per feature._

Two terms used below: the *TCB* (trusted computing base) is the code whose
correctness the acceptance verdict depends on (spec §1.1), and a `.lara` file
is the checked surface artifact; the README's running example shows what one
looks like.

## 1. Decision

Natural language meets LARA at three layers, and the three get different
answers. The split is by **trust direction**, not by convenience.

| # | Layer | Direction | Policy |
| --- | --- | --- | --- |
| 1 | Verified surface (`.lara`) | in, trusted | Gets **more readable**, never **natural**. |
| 2 | Producer (`Lara.Json` / the LLM elaborator) | in, untrusted | The **only** place NL is an input. |
| 3 | Verdicts, rejection reasons, reports | out | **Free** — exploit it. |

Layer 1 is inside the TCB, so anything it accepts is believed. Layer 2 is
outside it, so nothing it emits is believed until re-checked. Layer 3 reads
checked artifacts and feeds nothing back. The asymmetry in what NL is allowed to
do at each layer is exactly the asymmetry in what a mistake there would cost.

## 2. Layer 1 — readable, not natural

**The precedent is Isar, not the controlled-natural-language one.** A small,
rigid keyword grammar that reads aloud as prose but never pretends to parse
prose. The alternative lineage — controlled natural languages such as Attempto
ACE and Naproche — accepts a *fragment* of English, and that is where the
usability wall sits: a surface that looks like English but parses a fragment has
an **invisible parse boundary**, so every rejection feels arbitrary to the
author who cannot see where the fragment ends.

"Feels arbitrary" is fatal here specifically. The surface's job is
**auditability** — a human must be able to read what the checker actually saw —
and that requires determinism, not naturalness. A rejection a reviewer cannot
localize defeats the purpose of having a readable artifact at all.

**Calibration baseline: Python readability.** The audience is researchers who
read code, not PL specialists. "More readable" is measured against that bar and
not against English.

**The line has held so far, and it is checkable.** `docs/lara-surface-grammar.md`
is frozen at `lara-syntax@0.10`. For the named certificate spellings it records
— `@0.6`, `@0.8`, `@0.9`, `@0.10` — the grammar states the invariant that keeps
them honest: "None of these additions changes a lexer or parser rule, and each
successful named form lowers to the numeric spelling's exact bytes."

**NL-in through the verified parser is permanently out of scope.** This is not
a "not yet". A proposal to accept prose at layer 1 reopens this note; it is not
a per-feature judgment call.

## 3. Layer 2 — NL as input belongs exclusively to the untrusted producer

`docs/spec.md` §1.1 already places the elaborator **outside the TCB**, and §11
makes the first of its six logged lowering tasks "natural-language proposition
formalization". The claim triple (§3.1) carries the same boundary in the data:
`nl` is the human-facing text, `formal` is the checkable target, and the
`binding` between them is an **untrusted, audited annotation** — never a checked
one.

Two mechanisms make that sound, and they are what any layer-2 feature inherits:

- **Replay.** Nothing a producer emits is trusted until it is re-checked by
  trusted code. Per spec §1.1, "a defect outside [the TCB] cannot [make the
  checker accept an invalid certificate], because every untrusted output is
  re-checked by trusted code before it is believed."
- **The binding audit.** Prose-to-formal agreement is confirmed by a *human*,
  not by the checker — the pipeline is `scripts/binding-audit.hs` and
  `measurements/binding-audit/`, and executing it is
  separate follow-up work.

The consequence worth stating plainly, because it is the one an ease-of-use
proposal will try to route around: **checker acceptance establishes structural
validity only.** An NL-in feature cannot be made safe by making the producer
better. It is safe only if a human audits the binding, or if the checker never
had to trust it.

## 4. Layer 3 — NL as output is free; exploit it

Verdicts, rejection reasons, and reports derive from already-checked artifacts
and feed nothing back into the checker, so improving their prose cannot affect
what is accepted. This is the layer where naturalness is pure upside, and the
precedent to borrow is the Rust/Elm error-message discipline: say what went
wrong, where, and what would fix it.

One constraint, and one clarification:

- **A rendering must stay a rendering.** The moment an output becomes an input
  — a suggested fix the tool applies, a generated prose form the author is meant
  to paste back — it is a layer-1 or layer-2 change and must be argued there.
- **"Free" describes the prose, not the templates.** The rejection surface is
  normative and pinned (`docs/rejection-surface.md`; surface grammar H.5 fixes
  the eight `CertNd*` templates verbatim), and `scripts/differential.sh`
  byte-compares the two drivers' stdout and exit code. Improving a message is a
  surface change with a gate, not an unconstrained edit.

Landed under this heading: an R13 names its premise slots by source name,
and it prints the authored spelling of every atom it names. The residual —
binder names — is recorded
as an honest boundary rather than closed, because the only sound fix is a
backend-seam change; see §6.

## 5. The design rule

> Every ease-of-use feature must **remove transcription, never checking**.

A convenience crosses the line the moment the checker sees something the author
did not legibly write. A convenience that removes only what the elaborator can
reconstruct *and verify* is safe indefinitely.

At layer 1 the rule has an **executable form**: the readable spelling must lower
to the terse spelling's exact bytes. If it does, nothing the checker sees
changed, and the convenience provably removed transcription rather than
checking. Every surface version to date satisfies it:

| Version | What it removed from the author's hands | Reconstructed by |
| --- | --- | --- |
| `@0.4` | repeated ground terms | expansion of the presentation-only `let` table (Appendix C) |
| `@0.5` | transcribed theta | premise resolution (inferred-theta form) |
| `@0.6` | certificate slot arithmetic — `(prem e4)` for `(prem 0)` | premise resolution, lowered to the canonical numeric slot |
| `@0.7` | *(removes surface forms, adds none — the inverse move, and trivially safe)* | — |
| `@0.8` | slot references by position where a premise **label** exists | the citing rule's declared premise labels |
| `@0.9` | hand-computed de Bruijn indices in `nd@1` proof terms | named presentation over the unchanged kernel |
| `@0.10` | opaque encoded atom keys in `nd@1` annotations | source propositions, lowered through the shared encoder |

The pattern is the point: each one deleted a *transcription step the author
could get wrong*, and none of them changed what the kernel checks.

## 6. What this rule does not decide

The rule says whether a convenience is **permissible**, not whether it is
**worth building**. Those come apart, and #151 is the worked case: the binder
half of the `nd@1` diagnostics is squarely layer 3 and therefore permitted, but
the only sound implementation replaces the registered-backend seam's flat
`String` rejection with a structured one — a shared seam that `ord@1` and `ra@1`
also implement, and that the Lean side mirrors. Permitted, and still correctly
deferred on cost.

It also does not license the third option in that issue's menu: a *best-effort*
reconstruction outside the adapter would duplicate the checker's own scoping
rules and could print a **wrong** name. Under this note's framing that is worse
than printing an index — it is a layer-3 rendering that silently stops being
faithful to the checked artifact.

## 7. Consequences

- `Lara.Json` (the LLM
  producer surface) is the layer-2 instance. It stays deferred; this note is
  its upstream policy, so it starts from a settled boundary rather than
  reopening one.
- **Scope split.** The core language may cite the design rule and layer 1
  as a language-design commitment. Layer-2 evaluation — how faithfully a
  producer lowers prose — is deferred future work, along with #52.
- Future ease-of-use proposals cite this note. A proposal that keeps layer 1
  deterministic and lowers to identical bytes needs no re-litigation; one that
  does not is a change to *this* document first.
