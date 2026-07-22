
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
- When a value carries an invariant the frontend must not forge (e.g. an atom is
  `show . nf` of a normalized `Prop`), hide the constructor and expose it only
  through the sanctioned smart constructor / decoder, with an `.Internal` module
  as the test escape hatch (see `AtomId` / `Lara.Strict.ND.Internal`).
- The pre-parse wire token (`SExpr.SAtom`) is the one place a plain `String` is
  correct — it is untyped by design, like a JSON lexer's string node. Parse it
  into the symbolic core at the boundary; don't push surface concerns inward.

## ARA: agent-native research artifacts
This project uses ARA (https://github.com/ARA-Labs/Agent-Native-Research-Artifact).
Route research work to the matching ARA skill:
- At the END of every research or coding session → run `/research-manager` to
  capture decisions, experiments, dead ends, and claims into the `ara/` artifact.
- When turning an existing paper, repo, or notes into a structured artifact →
  run `/compiler <path>`.
- Before trusting, publishing, or submitting an artifact → run `/rigor-reviewer <dir>`.
- To inspect the full research trajectory as a process map → run `/research-visualizer <ara-dir>`.
- To answer "what should I try next / why did this work / what if I change X" →
  run `/research-foresight <ara-dir> "<question>"`.
- When an artifact is ready to publish and list on the ARA Hub → run `/submit-ara <dir>`.
