
## Mechanization discipline
After each stage of work, mechanize everything that is provable now. As soon as a
definition is frozen and corpus-independent, port it to the Lean development
(`lean/`) and prove its metatheory — do not defer provable results to a later
milestone. Keep `AxCheck.lean` covering every new theorem; proofs must stay
`sorry`-free and within the standard axiom trio (`propext`, `Classical.choice`,
`Quot.sound`). Haskell property tests are conformance evidence, not soundness;
the Lean proofs carry soundness, so land them alongside the code that frozen
definitions enable.

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
