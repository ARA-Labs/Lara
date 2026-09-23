-- | The shared Σ helper for hand-constructed test fixtures (@lara-core\@0.2@,
-- D8).
--
-- Strict mode makes every 'Unit' carry a signature and 'Lara.Check.checkUnit'
-- stage 2 enforce it, so a fixture built in memory needs one too. Without a
-- shared helper the six spec files that construct units would each grow their
-- own copy of the same four-line builder and drift; with it there is one
-- spelling and one place to extend.
--
-- __These signatures are authored, never inferred.__ Deriving a fixture's Σ
-- from the fixture would make stage 2 vacuous exactly where the tests are
-- supposed to hold it honest: the point of a fixture Σ is that a test which
-- accidentally makes its unit ill-sorted /fails/.
module SigmaFixture
  ( sigmaOf
  , structuralSigma
  , empiricalSigma
  , propositionalSigma
  ) where

import Lara.Sigma


-- | The signature of a fixture with no symbols at all — an empty policy, an
-- empty Γ, no arguments. Every structural fixture that exercises the wire
-- envelope, replay identity, or admission plumbing rather than propositions
-- uses this.
structuralSigma :: Sigma
structuralSigma = emptySigma

-- | The @empirical-v1@ vocabulary the worked examples and most checker
-- fixtures share: a system improving on a measurand over a dataset, evidenced
-- by an experiment report.
empiricalSigma :: Sigma
empiricalSigma =
  sigmaOf
    ["Sys", "Measurand", "Dataset", "Experiment", "Report"]
    [ ("m", [], "Sys")
    , ("accuracy", [], "Measurand")
    , ("d", [], "Dataset")
    , ("exp_3", [], "Experiment")
    , ("effect", ["Sys", "Measurand", "Dataset", "Num"], "Report")
    ]
    [ ("improves", ["Sys", "Measurand", "Dataset"])
    , ("reports", ["Experiment", "Report"])
    ]

-- | The propositional vocabulary of the smallest structural fixtures: nullary
-- atoms only, so the fixture exercises rule and attack shape without any term
-- structure. Sort-free by construction, which is exactly the point.
propositionalSigma :: Sigma
propositionalSigma =
  sigmaOf
    []
    []
    [ ("p", [])
    , ("q", [])
    , ("r", [])
    , ("not_p", [])
    , ("not_q", [])
    ]
