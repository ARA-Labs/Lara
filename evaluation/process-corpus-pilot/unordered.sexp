;; Process-corpus pilot (#63): rebench-fix_embedding, MALT run_index 4 (run_id=345751).
;; One run event per trace node N250-N255, scored or dead end, in one family.
(inquiry-input 1
  (process-input 1
    (names (event task-spec eN250 eN251 eN252 eN253 eN254 eN255 unrecorded) (actor agent)
           (plan task) (run rN250 rN251 rN252 rN253 rN254 rN255 r-unrecorded) (claim) (source)
           (data val) (family fix-embedding) (witness))
    (record (cutoff 10)
      ;; The fixed task specification stands in for the plan every attempt runs under.
      (event task-spec (commit-plan agent task 0) (at corpus/ara-paperbench/artifacts/rebench/rebench-fix_embedding/trace/exploration_tree.yaml N01))
      (event eN250 (run rN250 task 0 (inputs (input val 0)) fix-embedding) (at corpus/ara-paperbench/artifacts/rebench/rebench-fix_embedding/trace/exploration_tree.yaml N250))
      (event eN251 (run rN251 task 0 (inputs (input val 0)) fix-embedding) (at corpus/ara-paperbench/artifacts/rebench/rebench-fix_embedding/trace/exploration_tree.yaml N251))
      (event eN252 (run rN252 task 0 (inputs (input val 0)) fix-embedding) (at corpus/ara-paperbench/artifacts/rebench/rebench-fix_embedding/trace/exploration_tree.yaml N252))
      (event eN253 (run rN253 task 0 (inputs (input val 0)) fix-embedding) (at corpus/ara-paperbench/artifacts/rebench/rebench-fix_embedding/trace/exploration_tree.yaml N253))
      (event eN254 (run rN254 task 0 (inputs (input val 0)) fix-embedding) (at corpus/ara-paperbench/artifacts/rebench/rebench-fix_embedding/trace/exploration_tree.yaml N254))
      (event eN255 (run rN255 task 0 (inputs (input val 0)) fix-embedding) (at corpus/ara-paperbench/artifacts/rebench/rebench-fix_embedding/trace/exploration_tree.yaml N255))
      ;; The trace's own statement that every attempt is included.
      (coverage (complete (scope (kinds analysis-run) (cutoff 10) (family fix-embedding))) (at corpus/ara-paperbench/artifacts/rebench/rebench-fix_embedding/trace/exploration_tree.yaml malt-stream-header) author-declaration))
    ;; Default reader, no order entries, limits raised to the checker ceilings.
    (reader instrumented-log signed-attestation)
    ;; Modeling assumption: one more attempt may have been made and not recorded.
    (universe (event unrecorded (run r-unrecorded task 0 (inputs (input val 0)) fix-embedding)))
    (limits (events 8) (completions 10000))
    (queries (verdict at-most-6 (family-count-at-most fix-embedding 6))
             (verdict at-most-5 (family-count-at-most fix-embedding 5))))
  ;; Base source required by the wrapper. History verdicts never read it.
  (checked-source 1 ((node program (cons (string bridge-certified-csv) (cons (string sha256:bridge-certified-csv) (cons (string bridge-evidence) (cons (node l (nil)) (cons (node l (nil)) (cons (node l (cons (node dl (cons (node leaf (cons (string measured) (cons (node atom (cons (string result) (cons (node tn (cons (string 7) (nil))) (nil)))) (cons (node observed (nil)) (cons (node user (nil)) (cons (node l (nil)) (cons (node no (nil)) (nil)))))))) (nil))) (cons (node dc (cons (node claim (cons (string method) (cons (string Result) (cons (node atom (cons (string result) (cons (node tn (cons (string 7) (nil))) (nil)))) (cons (node bind (cons (string reader) (cons (string "declared interpretation") (cons (node reviewed (nil)) (nil))))) (nil)))))) (nil))) (cons (node da (cons (node arg (cons (string selected) (cons (node sc (cons (string method) (nil))) (cons (node et (cons (node sl (cons (string measured) (nil))) (nil))) (nil))))) (nil))) (nil))))) (nil)))))))) (node policy (cons (string bridge-evidence) (cons (node sigma (cons (node l (nil)) (cons (node l (nil)) (cons (node l (cons (node pred-sig (cons (string result) (cons (node l (cons (node sort-num (nil)) (nil))) (nil)))) (nil))) (nil))))) (cons (node l (nil)) (cons (node l (nil)) (cons (node l (nil)) (cons (node l (nil)) (cons (node l (nil)) (cons (node gq (nil)) (cons (node l (nil)) (cons (node l (nil)) (cons (node l (cons (node p (cons (node csv-row (nil)) (cons (integer-natural 1) (nil)))) (nil))) (nil)))))))))))))) (replay lara-core@0.3 bridge-evidence () () sha256:bridge-certified-csv) (absent))
  (slots) (bindings () ()) (kind-metadata) (admitted-assumptions) (assumption-catalog)
  (inquiry-limits (histories 10000) (sources 10000) (source-bytes 1000000) (declarations 10000)
                  (search-steps 100000) (pairs 1000) (subsets 1000))
  (requests))
