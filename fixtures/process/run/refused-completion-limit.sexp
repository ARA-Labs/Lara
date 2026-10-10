;; process-input 1 fixture
(process-input 1
  (names (event commit read run early-read) (actor alice) (plan plan) (run run0) (claim c0) (source) (data test) (family fam) (witness w0))
  (record (cutoff 10)
    (event commit (commit-plan alice plan 0) (at "experiments/plan.md" commit-v0))
    (event read (access alice test evaluation) (at "logs/access.md" read-test 12 18))
    (event run (run run0 plan 0 (inputs (input test 0)) fam) (at "experiments/run0.md" run0))
    (order commit read (at "logs/access.md" after-commit 20 21))
    (submit c0 w0))
  (reader instrumented-log signed-attestation)
  (universe (event early-read (access alice test evaluation)))
  (limits (events 8) (completions 1))
  (queries (verdict precommitted (run-precommitted run0)) (verdict predictable (predictable))))
