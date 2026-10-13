# Task P9-02

Claim `c0` is published with witness `w0` under the observed-only profile. Two admissible histories differ only in which run's result was captured. Decide whether the witness passes its audit in every completion, and name the distinguishing event of each completion where it fails.

Answer fields:

- `witness_passes_every_completion`: true | false
- `failing_completion_events`: list of the distinguishing event names (e.g. ["some-event"]) of completions where the audit fails; [] if none
