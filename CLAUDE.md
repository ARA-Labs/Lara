
## Task tracking: issues, not a file
Open follow-up work lives in GitHub issues. There is no `TODOS.md` and no other
in-repo backlog file; do not create one.
- When a change defers something actionable, open an issue (`gh issue create`)
  and reference it from the PR. A deferral recorded only in a commit message or
  a code comment is not tracked.
- An issue states the work, why it matters, and what it costs — especially when
  the cost is a corpus regeneration or a freeze-tag bump, which must be budgeted
  rather than discovered.
- Issues track *work*; `docs/` records *decisions*. A frozen contract, a settled
  design, or a rejected alternative belongs in a `docs/` record even when the
  issue that produced it closes.
- `plans/` holds only living research documents and implementation plans whose
  work has **not** landed; a plan that is executed gets deleted, with anything
  durable moved into `docs/` first. A partially executed plan stays, carrying a
  status banner saying which tasks remain.

## Mechanization discipline
After each stage of work, mechanize everything that is provable now. As soon as a
definition is frozen and corpus-independent, port it to the Lean development
(`lean/`) and prove its metatheory — do not defer provable results to a later
milestone. Keep `AxCheck.lean` covering every new theorem; proofs must stay
`sorry`-free and within the standard axiom trio (`propext`, `Classical.choice`,
`Quot.sound`). Haskell property tests are conformance evidence, not soundness;
the Lean proofs carry soundness, so land them alongside the code that frozen
definitions enable.

## Keep the compiler core symbolic
Keep the compiler core (checker, inference, normalization, the AST) symbolic so
the frontend keeps maximum freedom to design the concrete syntax. Concrete,
stringly-typed values live only at the decode boundary; the kernel manipulates
closed sum types and distinct newtyped symbols, never raw strings whose meaning
depends on surface syntax. Concretely:
- A fixed vocabulary (keywords, tags, modes) is a closed sum type, not a set of
  string literals. Give it one `toString`/`parse` table so the concrete spelling
  exists in exactly one place (see `Tag` in `Lara.Strict.ND`).
- A domain-meaningful identifier is its own `newtype`, never bare `String`
  (`Pred`, `FunSym`, `AtomId`, and the `*Id` classes in `Lara.AST`). Separate
  namespaces get separate types so they cannot be swapped silently.
- When a value carries an invariant the frontend must not forge (e.g. an ND
  atom is the shared UTF-8 framed `encodeAtomKey` of a normalized `Prop`), hide
  the constructor and expose it only through the sanctioned smart constructor /
  decoder, with an `.Internal` module as the test escape hatch (see `AtomId` /
  `Lara.Strict.ND.Internal`).
- The pre-parse wire token (`SExpr.SAtom`) is the one place a plain `String` is
  correct — it is untyped by design, like a JSON lexer's string node. Parse it
  into the symbolic core at the boundary; don't push surface concerns inward.

## Module size is a guideline, not a gate
The global coding style's file-length advice (split around 400 lines) is good
practice and worth following by default, but nothing in this repo enforces it and
no CI step measures it. Split a module when there is a nameable seam — a group of
definitions with its own vocabulary, its own dependencies, or its own reason to be
read alone — and treat length as a hint that such a seam may have appeared, never
as the reason on its own. A module stays as it is when it is long because it is
well documented, or because what it owns is genuinely one thing (`Lara.Syntax`,
`Lara.Wire`, `Lara.BindingAudit` are all past the guideline by design). See
`docs/mutate-module-ownership-decision.md` for the worked case, including why the
one namespace that had a hard bound no longer does.

## ARA: agent-native research artifacts
This project uses ARA (https://github.com/ARA-Labs/Agent-Native-Research-Artifact).
Update `ara/` and run `/research-manager` only when a session:
- introduces a new feature or materially changes an existing feature, design, or theory; or
- runs or interprets an experiment.

Do not update `ara/` or run `/research-manager` for routine next-step guidance,
PR reviews, or review/request-change resolution unless that work crosses one of
the thresholds above.

A corollary (settled on #333's review): a session record's `logic_revisions:`
`before`/`after` is what a Stage 4 edit wrote *on that turn* — a historical
snapshot, not a live mirror of `ara/logic/`. When review-round fixes correct
`ara/logic/` wording without crossing a threshold above, the earlier turn's
`logic_revisions` entry is expected to go stale relative to the now-corrected
logic file; that staleness lives in the trace where it happened, not as a
rewrite of the original entry. The logic file itself is always the current
state.

Route qualifying research work to the matching ARA skill:
- At the END of a qualifying session → run `/research-manager` to capture the
  feature/design/theory change or experiment in the `ara/` artifact.
- When turning an existing paper, repo, or notes into a structured artifact →
  run `/compiler <path>`.
- Before trusting, publishing, or submitting an artifact → run `/rigor-reviewer <dir>`.
- To inspect the full research trajectory as a process map → run `/research-visualizer <ara-dir>`.
- To answer "what should I try next / why did this work / what if I change X" →
  run `/research-foresight <ara-dir> "<question>"`.
- When an artifact is ready to publish and list on the ARA Hub → run `/submit-ara <dir>`.
