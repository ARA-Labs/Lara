;; D7, record version 2: version 1 plus the author's completeness note.
(inquiry-input 1
  (process-input 1
    (names (event plan-commit test-read eval-run unlogged-read) (actor analyst)
           (plan analysis-plan) (run eval) (claim) (source) (data test-set)
           (family primary) (witness))
    ;; What the natural-language record says, one entry per sentence it cites.
    (record (cutoff 10)
      (event plan-commit (commit-plan analyst analysis-plan 0) (at record/plan.md plan-v0))
      (event test-read (access analyst test-set evaluation) (at record/access-log.md test-read))
      (event eval-run (run eval analysis-plan 0 (inputs (input test-set 0)) primary) (at record/eval-run.md eval))
      (order plan-commit test-read (at record/access-log.md after-commit))
      ;; The author's own note claims the log is complete. The reader does not
      ;; admit author declarations, so the runner does not apply it.
      (coverage (complete (scope (kinds data-access) (cutoff 10))) (at record/access-log.md author-coverage) author-declaration))
    ;; The reader admits attestations from instrumented logs and signed attestations.
    (reader instrumented-log signed-attestation)
    ;; Modeling assumption: one more evaluation read may have happened off the record.
    (universe (event unlogged-read (access analyst test-set evaluation)))
    (limits (events 8) (completions 1000))
    (queries (verdict precommitted (run-precommitted eval))))
  ;; Base source required by the wrapper. History verdicts never read it.
  (checked-source 1 ((node program (cons (string bridge-certified-csv) (cons (string sha256:bridge-certified-csv) (cons (string bridge-evidence) (cons (node l (nil)) (cons (node l (nil)) (cons (node l (cons (node dl (cons (node leaf (cons (string measured) (cons (node atom (cons (string result) (cons (node tn (cons (string 7) (nil))) (nil)))) (cons (node observed (nil)) (cons (node user (nil)) (cons (node l (nil)) (cons (node no (nil)) (nil)))))))) (nil))) (cons (node dc (cons (node claim (cons (string method) (cons (string Result) (cons (node atom (cons (string result) (cons (node tn (cons (string 7) (nil))) (nil)))) (cons (node bind (cons (string reader) (cons (string "declared interpretation") (cons (node reviewed (nil)) (nil))))) (nil)))))) (nil))) (cons (node da (cons (node arg (cons (string selected) (cons (node sc (cons (string method) (nil))) (cons (node et (cons (node sl (cons (string measured) (nil))) (nil))) (nil))))) (nil))) (nil))))) (nil)))))))) (node policy (cons (string bridge-evidence) (cons (node sigma (cons (node l (nil)) (cons (node l (nil)) (cons (node l (cons (node pred-sig (cons (string result) (cons (node l (cons (node sort-num (nil)) (nil))) (nil)))) (nil))) (nil))))) (cons (node l (nil)) (cons (node l (nil)) (cons (node l (nil)) (cons (node l (nil)) (cons (node l (nil)) (cons (node gq (nil)) (cons (node l (nil)) (cons (node l (nil)) (cons (node l (cons (node p (cons (node csv-row (nil)) (cons (integer-natural 1) (nil)))) (nil))) (nil)))))))))))))) (replay lara-core@0.3 bridge-evidence () () sha256:bridge-certified-csv) (absent))
  (slots) (bindings () ()) (kind-metadata) (admitted-assumptions) (assumption-catalog)
  (inquiry-limits (histories 1000) (sources 1000) (source-bytes 1000000) (declarations 1000)
                  (search-steps 100000) (pairs 1000) (subsets 1000))
  (requests))
