# Amber Liu on the future of the research-artifact format (The Startup Show, 2026)

_Reference note on the ARA founder's public argument for replacing the paper-PDF as the unit of
research knowledge — the producer-side thesis of the ecosystem LARA checks (spec §11, the ARA
lowering boundary). Source: "No More Human Scientists? She quit Meta's Superintelligence Lab to
redefine science.", The Startup Show, 19:07, https://www.youtube.com/watch?v=XTYsBTcLJeY.
Participants: The Startup Show (host) and Amber Liu, founder of ARA
(https://github.com/ARA-Labs/Agent-Native-Research-Artifact). Transcribed 2026-07-24._

> **Provenance flag.** The excerpt below is reconstructed from YouTube **auto-generated captions**,
> lightly cleaned (fillers removed, obvious recognition errors repaired, sentences joined). Wording
> is therefore approximate — verify against the video before quoting verbatim in the paper.
> Timestamps are from the caption track.

## Why this matters to LARA

LARA's programs are lowered *from* ARAs (spec §11); this interview is the clearest public statement
of what the ARA side believes an artifact should carry and why. Three of Liu's positions are load
bearing for LARA's design premises:

1. **The artifact carries claims linked to implementations and grounded results** ([09:01]) — the
   exact producer-side counterpart of LARA's evidence leaves with `refs`, and of the M0 default
   per-result-cell leaf grain.
2. **Failed attempts and the exploration trajectory are first-class content** ([09:01], [10:00]) —
   the corpus phenomena behind the M0-frozen defeat-layer conventions: the whole-trace attack walk
   and dead-end-as-support-or-attack (spec §7, C16).
3. **Storytelling is stripped; only "dry knowledge" remains** ([09:01]) — the reason LARA can
   demand explicit, typed support structure at all: the artifact format is already committed to
   machine-checkable content over narrative persuasion.

The interview is *motivational* context, not evidence: nothing here discharges a LARA claim, and
Liu's bandwidth argument ("AI scientists have infinite bandwidth") is an assumption of the
ecosystem, not something LARA's checker relies on.

## Excerpt: the format of research artifacts

**Host** [02:00]: Is gathering and processing information the problem you're solving mostly?

**Liu** [02:00]: Not really. A lot of people are working hard on building more intelligent AI
scientists — better literature review, better ideation, better experimenting. I'm taking a
different approach. No one is actually touching the ecosystem, the research infrastructure, of AI
scientists. For the past 100 years all those infrastructures and ecosystems were designed for human
researchers who have limited bandwidth — paper PDFs, the peer-review system, conferences — they are
all designed to accommodate the limited bandwidth of humans. But now AI scientists become a major
contributor of research; we should rethink the whole infrastructure from first principles, because
AI scientists can brainstorm, review literature, and experiment at infinite scale. The producer and
consumer have changed; then we should also change the infrastructure.

**Liu** [04:00]: For example, how should research knowledge be presented to AI scientists, rather
than just paper PDFs? A paper PDF is essentially designed for human reviewers — to convince them
with a very polished story in about eight pages. So it has to strip out very important details, the
thinking process, and failed attempts, because humans cannot read all of that. But those are very
important for AI scientists to understand, reproduce, and extend the research. That is why the
research ecosystem should be changed. The research artifact is the starting point: we argue that
the **format of research knowledge matters a lot more than you think**, because that is how
knowledge compounds — in human history, after humans invented language, that is when human wisdom
started accumulating. Similarly for the format of the research artifact: if we define it very well
for AI scientists, then we start compounding the knowledge.

**Host** [05:00]: So a big part would be pre-processing — changing the format, maybe from PDF to
XML, extracting the key content. Does it even need to be natural language?

**Liu** [05:00]: Maybe — but I still think natural language is a great invention, because it
contains all the different kinds of information. You can use a number to represent a parameter, but
you cannot explain what the parameter is, what its function is, without natural language. There are
many ways to represent research — code, formulas, numbers — but natural language is a superset of
all of them.

**Host** [06:00]: But natural language was invented for humans to communicate, so there is probably
a lot of inefficiency in it.

**Liu** [06:00]: It's an open question how to make it more token-efficient. An interesting example
is Chinese: modern Chinese is already shorter than English, and classical Chinese is shorter still
— eight characters can mean a paragraph today. It is just a matter of how we define the language;
maybe in the future there is a more token-efficient one.

**Host** [08:02]: You launched a paper — "the last human-written paper." How did that come about?

**Liu** [08:02]: That is the bigger picture: no one is caring about the underlying ecosystem for AI
scientists, and the most important thing is the **medium of research knowledge** — that is what I
want to innovate. AI scientists have infinite scale of brainstorming, literature review, and
experimenting; however, the underlying ecosystems still accommodate humans' limited bandwidth, and
the paper PDF is the clearest example — designed to convince human reviewers with a polished story.
It strips out the intermediate thinking process, the important parameter details, and the failed
attempts — and those are very important for follow-up researchers to understand, reproduce, and
extend the research. [09:01] Especially for AI scientists, because they have the bandwidth to read
everything you tried and every parameter you used, and then reproduce the results. So in the paper
we argue that we need a **new primitive for the research artifact**. We propose the **agent-native
research artifact**: a unit of research knowledge that contains only the dry knowledge, no
storytelling — conceptual-level claims linked to the corresponding implementations and the
corresponding ground-truth results, so the claims are grounded — and the whole exploration
trajectory of the research process. Then we can do a lot on top: version control, verification,
making sure the artifact is reproducible and complete.

**Host** [10:00]: The storytelling in papers is useful for human comprehension — a linear,
sequential logic chain. But machines don't think that way; they don't need that comprehension
layer. Stripping it also lets you process faster, because it is noise in the dataset.

**Liu** [10:00]: Yeah — trying to remove all the noise. And the research artifact can be ugly: we
tried a lot of things and failed a lot of times. But the AI scientist doesn't need to know who is
behind it; it needs to know **what was tried and what failed**, so it doesn't rework all the dead
ends.

## Positions distilled

| Timestamp | Position |
| --- | --- |
| [02:00] | Research infrastructure (PDF, peer review, conferences) encodes human bandwidth limits; with AI scientists as producers *and* consumers, rebuild it from first principles |
| [04:00] | The paper-PDF optimizes for persuading human reviewers; it deletes exactly what reproduction and extension need (details, thinking process, failed attempts) |
| [04:00]–[05:00] | The format of research knowledge is the compounding mechanism for knowledge, analogous to the invention of language |
| [05:00]–[06:00] | Natural language stays as the superset representation (numbers/code/formulas alone can't carry meaning), but token-efficiency of the representation is an open question |
| [09:01] | The proposed primitive: the agent-native research artifact — dry knowledge only, claims → implementations → grounded results, plus the full exploration trajectory; version-controlled, verifiable, reproducible, complete |
| [10:00] | Dead ends are content, not embarrassment: recording failures is what saves successor researchers from reworking them |

## Full transcript

The complete cleaned transcript (including the world-model and career discussion outside this
note's scope) was captured from the same caption track; regenerate with
`yt-dlp --skip-download --write-auto-subs --sub-langs "en.*" <url>` if needed.
