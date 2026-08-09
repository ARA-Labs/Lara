-- | The committed worked-example registry: __one__ list of
-- @(directory, policy basename)@ pairs, shared by every consumer.
--
-- Two consumers used to carry byte-identical copies of this list and had to be
-- edited in lockstep — @scripts\/gen-worked-examples.hs@ (which /writes/ each
-- @\<dir\>\/example.core.sexp@ and @\<dir\>\/expected.json@) and
-- @test\/WorkedExamplesSpec.hs@ (whose freshness property /re-derives/ those
-- same bytes and asserts they match). A list added to one and not the other
-- produces exactly the silent gap the freshness property exists to catch: a
-- generated anchor nothing re-derives, or a re-derivation of an anchor nothing
-- generates. Hence one source, in the library both already depend on.
--
-- Each entry names a self-contained paper artifact directory holding
-- @example.lara@, its co-located policy file, and the two derived files. The
-- artifact is always @example.lara@; only the policy basename varies, because
-- it must match the @policy \<name\>@ header the artifact declares.
--
-- This module is deliberately data-only: it names files, so it depends on
-- nothing in the checker core and cannot drag a surface concern into it.
module Lara.WorkedExamples
  ( workedExamples
  , workedExampleArtifact
  , workedExamplePolicy
  , workedExampleCore
  , workedExampleExpected
  ) where

-- | Every committed worked example, as @(directory, policy basename)@.
--
-- Ordering is the order the generator writes in and is not semantically
-- load-bearing; keeping it grouped by series (teaching, E, R, S, then the
-- multi-run studies) is a readability convention only.
workedExamples :: [(FilePath, FilePath)]
workedExamples =
  [ ("examples/A", "empirical-v1.policy.lara")
  , ("examples/B", "empirical-v1.policy.lara")
  , ("examples/E1", "empirical-v1.policy.lara")
  , ("examples/E2", "empirical-v1.policy.lara")
  , ("examples/E3", "empirical-v1.policy.lara")
  , ("examples/E4", "empirical-v2.policy.lara")
  , ("examples/E5", "empirical-v2.policy.lara")
  , ("examples/R1", "empirical-v1.policy.lara")
  , ("examples/R2", "strict-bad-v1.policy.lara")
  , ("examples/R3", "empirical-v1.policy.lara")
  , ("examples/S1", "strict-v1.policy.lara")
  , ("examples/S2", "ord-v1.policy.lara")
  , ("examples/S3", "ord-le-v1.policy.lara")
  , ("examples/S4", "ord-setting-v1.policy.lara")
  , ("examples/S5", "ord-ppl-v1.policy.lara")
  , ("examples/agreement-map", "agreement-v1.policy.lara")
  , ("examples/rebuttal-replay/round0", "rebuttal-v1.policy.lara")
  , ("examples/rebuttal-replay/round1", "rebuttal-v1.policy.lara")
  , ("examples/rebuttal-replay/round2", "rebuttal-v1.policy.lara")
  , ("examples/running-example/run1", "empirical-v1.policy.lara")
  , ("examples/running-example/run2", "empirical-v1.policy.lara")
  ]

-- | The artifact source of a worked-example directory.
workedExampleArtifact :: FilePath -> FilePath
workedExampleArtifact dir = dir ++ "/example.lara"

-- | The co-located policy of a @(directory, policy basename)@ entry.
workedExamplePolicy :: (FilePath, FilePath) -> FilePath
workedExamplePolicy (dir, base) = dir ++ "/" ++ base

-- | The derived canonical check-input anchor of a worked-example directory.
workedExampleCore :: FilePath -> FilePath
workedExampleCore dir = dir ++ "/example.core.sexp"

-- | The derived expected-verdict JSON of a worked-example directory.
workedExampleExpected :: FilePath -> FilePath
workedExampleExpected dir = dir ++ "/expected.json"
