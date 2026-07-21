# Venue decision: venue-agnostic work; POPL 2028 baseline, PLDI 2027 as a stretch

_Status: settled 2026-07-21. CFPs for PLDI 2027 / POPL 2028 are not yet out; the dates below are
anchored to the most recent known cycle and shifted forward one year — confirm when CFPs publish._

## Framing (important)

**The venue does not drive the work.** Building the new language and finishing its metatheory is the
same regardless of where we submit; the venue is a *write-up* decision made once the work lands. So
the schedule is driven by how long the work takes, not the other way around.

## Decision

- **Baseline: POPL 2028** (~Jul 2027 deadline, anchored to POPL 2027's 9 Jul). For a *new language*,
  ~1 year is the realistic time to build it and finish the metatheory. This is the default plan.
- **Stretch: PLDI 2027** (~Nov 2026 deadline, notify ~Mar 2027, anchored to PLDI 2026: submit
  13 Nov 2025 → notify 5 Mar 2026). Take this shot **only if we turn out to be unusually
  productive** and the language + system are compelling by ~Nov 2026. Not a committed first shot.

Because a PLDI rejection (~Mar 2027) still lands ~4 months before the POPL deadline (~Jul 2027), the
stretch shot is essentially free: if we try PLDI early and miss, we re-spine as a theory paper and
submit to POPL on the baseline schedule anyway. Sequential, so no concurrent-submission conflict.

## Why this ordering

LARA is a new language *with* a new metatheory calculus plus an implementation — dual-fit for PLDI
and POPL (both use the same SIGPLAN `acmart` template, which is why they look interchangeable; they
are not). Every top PL paper needs one load-bearing **spine**; a paper that is 60% calculus and 60%
system gets dinged by both committees for the underdeveloped other half.

Spine assignment per write-up:
- **POPL (baseline)** — spine = calculus + metatheory (soundness, nf/≡ carve-out, Lean proof). The
  new-language design remains but as motivation/demo, not the load-bearing contribution.
- **PLDI (stretch)** — spine = language + system (+ evaluation). Calculus is the foundation section
  establishing well-definedness/soundness; metatheorem is a supporting pillar, not the headline.

## Author-context note

Lead author's PhD was in software security / software engineering, now shifting into PL. The
SE/security background is a direct asset if we take the PLDI stretch (language/eval framing). Caveat
carried forward: PL reviewer norms weight formal precision and mechanized proofs more heavily than
SE/security venues — so a PLDI paper's foundation section must still be airtight, and the POPL
baseline lives or dies on the mechanization.

## Decision trigger for the stretch

Around ~Nov 2026, check: is the language + system compelling *and* is enough of the metatheory in
place? If yes → take the PLDI 2027 shot. If not → stay on the POPL 2028 baseline, no penalty. The
work itself proceeds identically either way.

## Considered and ruled out: OOPSLA

OOPSLA (the third SIGPLAN flagship; PACMPL; twice-yearly rolling deadlines ~Apr/~Oct; frequently
co-located with ISSTA under SPLASH, hence SE-friendly) was considered and rejected as a target for
LARA. Its sweet spot is the *programming model as experienced* — new paradigms, case studies,
empirical PL. LARA's load-bearing contribution is a **new metatheory calculus with mechanized
proofs**, a formal result. To an OOPSLA committee that spine reads as under-motivated ("where's the
programming-model insight / the case study?"), and it spends the Lean mechanization at a venue that
values it less than POPL does. SE-friendliness (ISSTA co-location) is not the axis LARA's
contribution lives on. Verdict: not a fit.
