-- | The seeded mutation suite (M5, T1) as a standing test.
--
-- Three properties hold the committed @fixtures\/mutants\/@ suite:
--
--   * __specified outcomes__: every manifest row's mutant produces exactly its
--     specified outcome through the production pipeline — the pinned rejection
--     class via 'Lara.Driver.runCheck', an all-@undec@\/@contested@ accept for
--     the cycle family, or — for the @malformed\/@ negative half — a
--     codec-boundary decode failure carrying the operator's pinned diagnostic
--     substring (manifest column @hs-diagnostic@, from 'codecDiagnostics'):
--     any-failure would let a deleted codec check stay green via a different
--     downstream check.
--   * __seeded reproducibility__: re-deriving the whole suite from the
--     committed worked-example anchors with the @Lara.Mutate.*@ generators
--     (same "Lara.Mutate".@mutationSeed@) reproduces the committed files and manifest
--     byte-for-byte. A drifted base anchor, seed, or operator fails here —
--     regenerate with @scripts\/gen-mutants.hs@.
--   * __coverage__: every executable rejection class
--     (R1\/R3\/R4\/R5\/R6\/R7\/R9\/R10\/R11\/R12\/R13) is exercised by at
--     least one generated mutant, plus the codec negatives and the
--     specified-status cycle family — the rejection-class half of the T1
--     exit criterion, measured from the manifest rather than
--     asserted in prose. The other half — generators over T2 corpus units,
--     and generated mutants exercising every status\/attack kind — stays
--     open until the corpus units exist.
--
-- The Lean half of the obligation (byte-identical verdicts) is
-- @scripts/differential.sh@, which walks @fixtures\/mutants\/*.sexp@ as
-- positive anchors and @fixtures\/mutants\/malformed\/*.sexp@ as negative
-- anchors through both drivers.
module MutationSpec (mutationSpecProps) where

import Test.QuickCheck

import Data.List (isInfixOf, sort, tails)
import Data.Maybe (mapMaybe)

import Lara.AST
  ( ArgId (..)
  , Assurance (..)
  , BackendId (..)
  , Attack (..)
  , Cert (..)
  , DupGroup (..)
  , GroupConflictMode (..)
  , GroupId (..)
  , Label (..)
  , LeafId (..)
  , Pred (..)
  , RejectClass (..)
  , Rejection (..)
  , Rule (..)
  , Status (..)
  , Step (..)
  , SupportTerm (..)
  , TheoryDigest (..)
  , Unit (..)
  )
import Lara.Blocked (prune, pruneChecked, retainedAttackIndices, retainedIndices)
import Lara.Diagnostics
  ( Constituent (..)
  , LocatedRejection (..)
  , constituentListText
  , parseConstituentList
  , seededSitesList
  )
import Lara.Driver (runCheck, runCheckLocated)
import Lara.Mutate
  ( Expected (..)
  , Mutant (..)
  , MutationOp (..)
  , OpFamily (..)
  , expectedText
  , familyText
  , mutationBases
  , opFamily
  , opName
  , parseExpected
  )
import Lara.Mutate.Accept (acceptMutants, acceptStructureOk)
import Lara.Mutate.Codec (codecMutantsForBase)
import Lara.Mutate.Cycle (cycleMutants)
import Lara.Mutate.Manifest (manifestFor, mutantPath)
import Lara.Mutate.Suite
  ( SiteOp (..)
  , corpusBudget
  , corpusMutants
  , corpusSweepReport
  , dropCoveringAttackSites
  , mutantsForBase
  , siteOps
  )
import Lara.Prop (Prop (..))
import Lara.Replay (CheckInput, inputReplayId, inputUnit, mkCheckInput)
import Lara.Sigma (declarePred)
import Lara.Strict (SExpr (..))
import qualified Lara.Strict.RA as RA
import Lara.Wire
  ( Outcome (..)
  , PublicStatus (..)
  , Verdict (..)
  , WireError (..)
  , decodeCheckInputFile
  , isPublished
  )

import CheckSpec (quarantiningConflictBase)
import TestReplay (testCheckInput)

suiteRoot :: FilePath
suiteRoot = "fixtures/mutants"

-- | One parsed manifest row: path relative to the suite root, family,
-- expected outcome, and — for codec rows — the pinned Haskell diagnostic
-- substring (empty otherwise). 'prop_seededReproducibility' ties the
-- diagnostic column back to 'codecDiagnostics', so asserting the column here
-- asserts the one table.
data Row = Row
  { rowPath :: FilePath
  , rowBase :: String
  , rowFamily :: String
  , rowOp :: String
  , rowExpected :: Expected
  , rowHsDiag :: String
  , rowSite :: String -- ^ raw @expected-location@ column (column 8)
  }
  deriving (Eq, Show)

readManifest :: IO [Row]
readManifest = do
  raw <- readFile (suiteRoot ++ "/MANIFEST.tsv")
  pure (mapMaybe parseRow (lines raw))
  where
    parseRow line = case splitTab line of
      [path, base, family, op, expected, hsDiag, _leanDiag, site]
        | not ("#" `isPrefix` path) ->
            (\e -> Row path base family op e hsDiag site) <$> parseExpected expected
      _ -> Nothing
    isPrefix p s = take (length p) s == p

splitTab :: String -> [String]
splitTab s = case break (== '\t') s of
  (field, '\t' : rest) -> field : splitTab rest
  (field, "") -> [field]
  (field, _) -> [field]

-- | The corpus units as mutation bases, in @corpus-units/MANIFEST.tsv@ order,
-- each labelled @\<artifact\>.\<claim_id\>@ and decoded from its committed
-- @unit.core.sexp@ (the exact list @scripts/gen-mutants.hs@ passes to
-- 'corpusMutants', so the re-derived suite matches byte-for-byte).
readCorpusBases :: IO [(String, CheckInput)]
readCorpusBases = do
  raw <- readFile "corpus-units/MANIFEST.tsv"
  let rows =
        [ (artifact, claimId)
        | ln <- drop 1 (lines raw)
        , not (null ln)
        , (_group : artifact : claimId : _) <- [splitTab ln]
        ]
  concat
    <$> mapM
      ( \(artifact, claimId) -> do
          let anchor = "corpus-units/" ++ artifact ++ "/" ++ claimId ++ "/unit.core.sexp"
          bytes <- readFile anchor
          case decodeCheckInputFile bytes of
            -- Fail loudly (as scripts/gen-mutants.hs does) rather than dropping the
            -- base, so a broken anchor surfaces here and not as a misleading
            -- "manifest is stale" mismatch from a silently-shortened base list.
            Left err -> fail (anchor ++ ": decode: " ++ show err)
            Right input -> pure [(artifact ++ "." ++ claimId, input)]
      )
      rows

-- | The outcome a mutant file actually produces, in manifest spelling.
actualOutcome :: String -> String
actualOutcome bytes = case decodeCheckInputFile bytes of
  Left _ -> expectedText ExpectCodecReject
  Right input -> case verdictOutcome (runCheck input) of
    Reject (RejectClass c) -> expectedText (ExpectClass c)
    Reject other -> "reject-" ++ show other
    -- An @evidence-blocked@ query has no four-state public status — spec §4.3 —
    -- so the accept is its own manifest class.
    Accept labels _ statuses
      | any (not . isPublished . snd) statuses -> expectedText ExpectEvidenceBlocked
      | not (null labels)
          && all ((== LUndec) . snd) labels
          && not (null statuses)
          && all ((== Published Contested) . snd) statuses ->
          expectedText ExpectAllContested
      | otherwise -> "accept-other"

-- | Every manifest row's mutant produces exactly its specified outcome. A
-- codec row must additionally fail with its operator's pinned diagnostic —
-- the check the operator targets, not just any decode failure.
prop_specifiedOutcomes :: Property
prop_specifiedOutcomes = once $ ioProperty $ do
  rows <- readManifest
  checks <- mapM checkRow rows
  pure $
    conjoin
      ( counterexample "mutant manifest is empty" (not (null rows))
          : checks
      )
  where
    checkRow row = do
      bytes <- readFile (suiteRoot ++ "/" ++ rowPath row)
      pure $ counterexample (rowPath row) $ case rowExpected row of
        ExpectCodecReject -> checkCodec row bytes
        -- An accept-family mutant's verdict can look all-undec/all-contested
        -- (a 2-cycle has both args undec), so check the single queried claim's
        -- status directly rather than through 'actualOutcome'.
        ExpectPrimaryStatus s -> primaryStatus bytes === Just s
        _ -> actualOutcome bytes === expectedText (rowExpected row)
    checkCodec row bytes = case decodeCheckInputFile bytes of
      Right _ ->
        counterexample "decoded cleanly instead of failing at the codec boundary" False
      Left (WireError ctx msg) ->
        let rendered = ctx ++ ": " ++ msg
         in conjoin
              [ counterexample
                  "manifest hs-diagnostic column is empty for a codec row"
                  (not (null (rowHsDiag row)))
              , counterexample
                  ( "failed the wrong codec check: expected a diagnostic containing "
                      ++ show (rowHsDiag row)
                      ++ ", got "
                      ++ show rendered
                  )
                  (rowHsDiag row `isInfixOf` rendered)
              ]

-- | Re-deriving the suite from the committed anchors reproduces the committed
-- files and manifest exactly (the seeded-reproducibility guard).
prop_seededReproducibility :: Property
prop_seededReproducibility = once $ ioProperty $ do
  derived <- concat <$> mapM deriveBase mutationBases
  corpusBases <- readCorpusBases
  let mutants =
        derived
          ++ cycleMutants
          ++ corpusMutants corpusBases
          ++ acceptMutants corpusBases
  committedManifest <- readFile (suiteRoot ++ "/MANIFEST.tsv")
  fileChecks <- mapM checkFile mutants
  pure $
    conjoin
      ( counterexample
          "MANIFEST.tsv is stale — regenerate with scripts/gen-mutants.hs"
          (manifestFor mutants === committedManifest)
          : fileChecks
      )
  where
    deriveBase base = do
      let anchor = "examples/" ++ base ++ "/example.core.sexp"
      bytes <- readFile anchor
      pure $ case decodeCheckInputFile bytes of
        Left _ -> []
        Right input -> mutantsForBase base input ++ codecMutantsForBase base bytes
    checkFile m = do
      committed <- readFile (suiteRoot ++ "/" ++ mutantPath m)
      pure $
        counterexample
          (mutantPath m ++ " is stale — regenerate with scripts/gen-mutants.hs")
          (mutantBytes m === committed)

-- | The rejection-class half of the T1 exit criterion, measured from the
-- manifest: every executable rejection class, the structural obligation-gate
-- reject (@reject-IncompleteArgument@, M5 T6), the codec negatives, and the
-- cycle family are witnessed. The status\/attack-kind half of the criterion
-- needs T2 corpus units and is not asserted here.
-- | The family vocabulary is well formed, independently of what the committed
-- suite happens to contain: 'opFamily' is surjective onto 'OpFamily', and
-- 'familyText' is injective.
--
-- Neither has a live violation — all 12 families are reachable and distinctly
-- spelled today — so this guards the shapes that only bite later. A family
-- constructor wired to no operator has a spelling that reaches no manifest
-- column and is therefore gated by nothing, and it would enter committed bytes
-- on its first real use. Two constructors sharing a spelling would silently
-- merge two families in column 3, which is the exact confusion a single
-- spelling table exists to prevent (review).
prop_familyVocabulary :: Property
prop_familyVocabulary =
  once $
    conjoin
      [ counterexample
          "opFamily is not surjective — some OpFamily constructor has no operator"
          ( sort (nubOrd (map opFamily [minBound .. maxBound :: MutationOp]))
              === [minBound .. maxBound :: OpFamily]
          )
      , counterexample
          "familyText is not injective — two families share a manifest spelling"
          ( length (nubOrd (map familyText allFamilies)) === length allFamilies
          )
      ]
  where
    allFamilies = [minBound .. maxBound :: OpFamily]

prop_mutationCoverage :: Property
prop_mutationCoverage = once $ ioProperty $ do
  rows <- readManifest
  let witnessed = sort (nubOrd (map rowExpected rows))
      families = sort (nubOrd (map rowFamily rows))
      wanted =
        ExpectCodecReject
          : ExpectAllContested
          : ExpectEvidenceBlocked
          -- The obligation-gate witness (M5 T6): `hole-obligation` is the one
          -- operator specified to `reject-IncompleteArgument`, so requiring the
          -- outcome here requires the operator to produce mutants of its class.
          : ExpectIncompleteArgument
          -- The attack-completeness witness, the same way:
          -- `drop-covering-attack` is the one operator specified to
          -- `reject-MissingConflict`.
          : ExpectMissingConflict
          : map ExpectClass [minBound .. maxBound]
  pure $
    conjoin
      [ counterexample
          ("outcome coverage incomplete — witnessed " ++ show (map expectedText witnessed))
          (all (`elem` witnessed) wanted)
      , -- Enumerated, never re-spelled: a hand-written copy of the table is a
        -- second place the spelling lives, and the one that shipped here had
        -- drifted to 10 of 12 — 'localization' and 'signature' (the largest
        -- family, 113 mutants) had no coverage assertion at all. Enumerating
        -- 'OpFamily' also means a renamed spelling fails HERE, as missing
        -- coverage, rather than only as a stale-fixture diff (review).
        counterexample
          ("family coverage incomplete — witnessed " ++ show families)
          (all (`elem` families) (map familyText [minBound .. maxBound]))
      , counterexample
          "quarantine-attacker mutation operator disappeared"
          ("quarantine-attacker" `elem` map rowOp rows)
      ]

-- | The @lara-core\@0.2@ signature closeout keeps one integrated stage-2
-- fixture for every Sigma well-formedness clause, plus both codec-boundary
-- corruptions of the new @sigma@ section. Exact one-row coverage prevents a
-- generator change from silently dropping a clause or multiplying the
-- dedicated negatives across every mutation base.
prop_sigmaFixtureCoverage :: Property
prop_sigmaFixtureCoverage = once $ ioProperty $ do
  rows <- readManifest
  let sigmaWfOps =
        [ OpSigmaDuplicateSort
        , OpSigmaShadowBase
        , OpSigmaDuplicateCon
        , OpSigmaDuplicatePred
        , OpSigmaConUndeclaredSort
        , OpSigmaPredUndeclaredSort
        ]
      codecSigmaOps = [OpCodecSigmaJunk, OpCodecSigmaOrder]
      rowsFor op = [r | r <- rows, rowOp r == opName op]
      oneR2 op =
        counterexample
          (opName op ++ ": expected exactly one reject-R2 fixture")
          (map rowExpected (rowsFor op) === [ExpectClass R2])
      oneCodec op =
        counterexample
          (opName op ++ ": expected exactly one diagnostic-pinned codec fixture")
          ( case rowsFor op of
              [r] -> rowExpected r == ExpectCodecReject && not (null (rowHsDiag r))
              _ -> False
          )
  pure $ conjoin (map oneR2 sigmaWfOps ++ map oneCodec codecSigmaOps)


-- | The located driver's contract, over every verdict-bearing mutant (the codec
-- rows do not decode): (1) the iron invariant @runCheck ≡ fst . runCheckLocated@
-- — a future-proofing guard should @runCheck@ ever be re-derived independently;
-- and (2) the non-definitional pairing — a @Reject@ verdict pairs with a
-- 'Just' located rejection whose class equals the verdict's, and an @Accept@
-- pairs with 'Nothing'. The T3 harness (@test\/MeasureSpec.hs@) will extend the
-- iron invariant over both the mutant and corpus-unit manifests.
prop_runCheckLocatedConsistent :: Property
prop_runCheckLocatedConsistent = once $ ioProperty $ do
  rows <- readManifest
  checks <- mapM checkRow [r | r <- rows, rowExpected r /= ExpectCodecReject]
  pure $
    conjoin
      (counterexample "no verdict-bearing rows found" (not (null checks)) : checks)
  where
    checkRow row = do
      bytes <- readFile (suiteRoot ++ "/" ++ rowPath row)
      pure $ counterexample (rowPath row) $ case decodeCheckInputFile bytes of
        Left err -> counterexample ("unexpected decode failure: " ++ show err) (property False)
        Right input ->
          let (verdict, located) = runCheckLocated input
           in conjoin
                [ counterexample "fst . runCheckLocated /= runCheck" (verdict === runCheck input)
                , counterexample
                    ("located-rejection contract violated: " ++ show (verdictOutcome verdict, located))
                    (contractHolds (verdictOutcome verdict) located)
                ]
    contractHolds outcome located = case (outcome, located) of
      (Reject rej, Just lr) -> lrRejection lr == rej
      (Accept{}, Nothing) -> True
      _ -> False

-- | The @expected-location@ column (column 8) is present exactly on the
-- verdict-bearing seeded-reject rows and round-trips through the one
-- 'constituentListText'\/'parseConstituentList' spelling (a non-empty ordered
-- list); the codec and cycle rows carry @-@ (no seeded site).
prop_expectedLocationColumn :: Property
prop_expectedLocationColumn = once $ ioProperty $ do
  rows <- readManifest
  pure $
    conjoin
      ( counterexample "mutant manifest is empty" (not (null rows))
          : [ counterexample
                (rowPath row ++ ": expected-location " ++ show (rowSite row))
                (wellFormed row)
            | row <- rows
            ]
      )
  where
    wellFormed row = case rowExpected row of
      ExpectClass _ -> sited row
      ExpectIncompleteArgument -> sited row -- single-seeded-site reject too
      ExpectMissingConflict -> sited row -- located at the uncovered pair
      _ -> rowSite row == "-"
    sited row = rowSite row /= "-" && roundTrips (rowSite row)
    roundTrips s = maybe False ((== s) . constituentListText) (parseConstituentList s)

-- | An operator's proposed sites, with each published ground truth as a plain
-- list. The enumerators return 'Lara.Diagnostics.SeededSites', which is
-- non-empty by construction; these properties inspect the /shape/ of
-- what was published — singleton versus composite — so they read the list.
publishedSites :: SiteOp -> Unit -> [(Expected, [Constituent], Unit -> Unit)]
publishedSites op u = [(e, seededSitesList ss, m) | (e, ss, m) <- siteSites op u]

-- | The whole answer key is pinned to the checker, the way
-- 'prop_conflictSiteMatchesChecker' pins the completeness mirror: for every
-- site every rejection-site enumerator ('Lara.Mutate.Suite.siteOps') proposes
-- — not just the seeded subset the committed suite carries — on the worked
-- examples, every corpus unit, and the quarantining fixture, the mutated unit
-- rejects with the site's specified outcome and 'runCheckLocated' reports
-- exactly the /head/ of the site's ordered ground-truth list (the
-- spec-order-first constituent; membership follows,
-- docs\/localization-metric-decision.md). A fail-fast checker witnesses only
-- the head in one run, so this property cannot gate the non-head elements of
-- a composite site; any operator publishing them owes them a gate of its own.
--
-- This is what turns the @expected-location@ column from a measured ground
-- truth into a gated one: 'Lara.Measure.detLocationMatch' compares
-- located-vs-seeded but flows into @measurements\/report.{json,tsv}@ and is
-- never asserted. The quarantining fixture is the discriminating base — every
-- committed base's §4.3 quarantine is the identity, so declared indices
-- coincide with checked ones there and only the fixture can catch an
-- enumerator publishing declared-space indices or striking pruned material
-- (an accepting no-op, which the specified-outcome half catches).
prop_siteMatchesChecker :: Property
prop_siteMatchesChecker = once $ ioProperty $ do
  corpusBases <- readCorpusBases
  anchors <- mapM readAnchorBase mutationBases
  let bases =
        [(b, i) | (b, Just i) <- anchors]
          ++ corpusBases
          ++ [("quarantining-conflict-fixture", testCheckInput quarantiningConflictBase)]
      -- Every base again with both index spaces skewed (review), so the
      -- rule-rooted enumerators — which the one committed quarantining base
      -- cannot reach, having no rules — are gated off the diagonal too.
      --
      -- Rebuilt against the base's /own/ replay id: re-deriving one would
      -- change the backend and policy the unit is checked under, and a
      -- cert-carrying base would then reject at the backend layer (R13)
      -- instead of at the seeded site.
      skewed =
        [ (b ++ "+skew", input')
        | (b, input) <- bases
        , let u = quarantineSkewed (inputUnit input)
        , isSkewed u
        , Right input' <- [mkCheckInput (inputReplayId input) u]
        ]
      sites =
        [ (base, siteOp op, input, expected, predicted, mutate)
        | (base, input) <- bases ++ skewed
        , op <- siteOps
        , (expected, predicted, mutate) <- publishedSites op (inputUnit input)
        ]
  pure $
    conjoin
      ( [ counterexample
            (opName (siteOp op) ++ ": no sites on any base — the operator would be ungated")
            (any (\(_, o, _, _, _, _) -> o == siteOp op) sites)
        | op <- siteOps
        ]
          ++ [ counterexample
                 (base ++ "/" ++ opName op ++ ": predicted " ++ show predicted)
                 (siteAgrees input expected predicted mutate)
             | (base, op, input, expected, predicted, mutate) <- sites
             ]
      )
  where
    readAnchorBase base = do
      bytes <- readFile ("examples/" ++ base ++ "/example.core.sexp")
      pure (base, either (const Nothing) Just (decodeCheckInputFile bytes))

    siteAgrees input expected predicted mutate =
      case mkCheckInput (inputReplayId input) (mutate (inputUnit input)) of
        Left err ->
          counterexample ("mutated unit failed to rebuild: " ++ show err) False
        Right mutated ->
          let (verdict, located) = runCheckLocated mutated
           in conjoin
                [ counterexample ("outcome was " ++ show (verdictOutcome verdict)) $
                    case specifiedRejection expected of
                      Just rej -> verdictOutcome verdict === Reject rej
                      Nothing ->
                        counterexample "site specified a non-rejection outcome" False
                , counterexample ("checker located " ++ show (fmap lrConstituent located)) $
                    case predicted of
                      [] -> counterexample "site published an empty ground-truth list" False
                      primary : _ -> fmap lrConstituent located === Just primary
                ]

    -- Every site enumerator specifies a rejection; the accept, cycle, and
    -- codec families are constructions, not sites.
    specifiedRejection e = case e of
      ExpectClass c -> Just (RejectClass c)
      ExpectIncompleteArgument -> Just IncompleteArgument
      ExpectMissingConflict -> Just MissingConflict
      _ -> Nothing

-- | Skew both index spaces of a base without changing what the checker sees.
--
-- 'quarantiningConflictBase' is the only committed base whose §4.3 quarantine
-- is not the identity, and it carries no rules and no rule-rooted argument —
-- so every @ruleSites@-based enumerator was exercised only where checked and
-- declared indices coincide, and a per-operator transposition would have
-- failed open (review). This derivation gives every base a skewed
-- sibling: it prepends an inconsistent duplicate-report group, a leaf-rooted
-- argument on one of its members, and an attack /targeting/ that argument, all
-- declared first.
--
-- Quarantine removes exactly the added material, so the checked unit is the
-- original base — same arguments, same attacks, same order, so the same
-- verdict — while every declared index is shifted by one (leaves by two). The
-- attack targets the added argument rather than issuing from it, so no
-- retained argument loses an incoming edge and nothing becomes
-- evidence-blocked by the skew ('CheckSpec.groupQuarantineLostEdgeUnit' is the
-- case that would).
--
-- Bases that already declare a group are returned unchanged: overriding
-- 'unitGroupMode' there could change the base's own verdict.
quarantineSkewed :: Unit -> Unit
quarantineSkewed u
  | not (null (unitGroups u)) = u
  | otherwise =
      u
        { unitSigma = declarePred skewP [] (declarePred skewQ [] (unitSigma u))
        , unitLeaves =
            [(skewLeafA, Prop skewP []), (skewLeafB, Prop skewQ [])] ++ unitLeaves u
        , unitArgs = (skewArg, SLeaf skewLeafA) : unitArgs u
        , unitAttacks = skewAttacks ++ unitAttacks u
        , unitGroups = [DupGroup (GroupId "mut_skew_g") [skewLeafA, skewLeafB]]
        , unitGroupMode = QuarantineOnConflict
        }
  where
    skewP = Pred "mut_skew_p"
    skewQ = Pred "mut_skew_q"
    skewLeafA = LeafId "mut_skew_a"
    skewLeafB = LeafId "mut_skew_b"
    skewArg = ArgId "mut_skew_arg"
    skewAttacks = [Undermine aid skewArg [] | aid <- take 1 (map fst (unitArgs u))]

-- | Whether the derivation actually skewed this base — a base it declined to
-- skew (one that already declares a group) contributes no direction evidence.
isSkewed :: Unit -> Bool
isSkewed u = retainedIndices (prune u) /= [0 .. length (unitArgs u) - 1]

-- | The sole declared index a rewrite touched: the one position at which the
-- lists differ, or the index of a lone appended entry. 'Nothing' when the
-- rewrite was not a single-site edit.
soleEdit :: (Eq a) => [a] -> [a] -> Maybe Int
soleEdit old new
  | length new == length old =
      case [i | (i, a, b) <- zip3 [0 :: Int ..] old new, a /= b] of
        [i] -> Just i
        _ -> Nothing
  | length new == length old + 1, take (length old) new == old = Just (length old)
  | otherwise = Nothing

atIx :: [a] -> Int -> Maybe a
atIx xs i
  | i >= 0, i < length xs = Just (xs !! i)
  | otherwise = Nothing

-- | The __direction__ of the index mapping, pinned for every enumerator
-- that publishes an indexed constituent, on bases where the two spaces
-- actually differ (review).
--
-- 'prop_siteMatchesChecker' pins that the published constituent is the one the
-- checker reports, but an enumerator that transposes /both/ maps — publishing
-- the declared index while rewriting the checked one — cancels to a pass on
-- any base whose quarantine is the identity, which is every committed base but
-- one. This property states the mapping itself: for each site, the declared
-- index the rewrite edited is exactly the one 'Lara.Blocked.retainedIndices'
-- (or 'Lara.Blocked.retainedAttackIndices') pairs with the published checked
-- index. A transposition fails it as soon as the two spaces differ, which
-- 'quarantineSkewed' arranges for every base.
--
-- The second half is the anti-vacuity gate, the sibling of
-- 'prop_siteMatchesChecker'\'s \"no sites on any base\" check: every operator
-- that publishes an indexed constituent — except the localization family,
-- whose composite lists are deferred to 'prop_localizationSites' — must have
-- at least one site on a skewed base where the checked index and the declared
-- index /differ/. Without it a future operator could satisfy the first half
-- everywhere by never being exercised off the diagonal — the exact gap this
-- property was added to close.
prop_siteDirectionSkewed :: Property
prop_siteDirectionSkewed = once $ ioProperty $ do
  corpusBases <- readCorpusBases
  anchors <- mapM readAnchorBase mutationBases
  let bases =
        [(b, inputUnit i) | (b, Just i) <- anchors]
          ++ [(b, inputUnit i) | (b, i) <- corpusBases]
          ++ [("quarantining-conflict-fixture", quarantiningConflictBase)]
      skewed = [(b ++ "+skew", quarantineSkewed u) | (b, u) <- bases]
      allSites =
        [ (base, siteOp op, u, predicted, mutate)
        | (base, u) <- skewed ++ bases
        , isSkewed u
        , op <- siteOps
        -- The localization family is deferred to its own gate,
        -- 'prop_localizationSites', which re-derives every published list
        -- from the mutant and the component enumerators on these same skewed
        -- bases — a stronger index-space pin than the sole-edit argument,
        -- which cannot apply here anyway: @retract-rule@ edits the policy (no
        -- indexed material moves), and the composites edit two constituents.
        , opFamily (siteOp op) /= FamLocalization
        , (_, predicted, mutate) <- publishedSites op u
        ]
      -- The sole-edit direction argument pairs ONE published index with ONE
      -- edited constituent, so the per-site check runs on singleton-published
      -- sites; the operator census below still reads every published list, so
      -- an undeferred composite-publishing operator cannot vanish from the
      -- anti-vacuity gate — it fails it until it carries an off-diagonal
      -- singleton or a gate of its own.
      sites = [(base, op, u, c, mutate) | (base, op, u, [c], mutate) <- allSites]
      indexed = [s | s@(_, _, _, c, _) <- sites, isIndexed c]
      isIndexed c = case c of
        CArgument _ -> True
        CAttack _ -> True
        _ -> False
      offDiagonal (_, _, u, c, _) = case c of
        CArgument ci -> retainedIndices (prune u) `atIx` ci /= Just ci
        CAttack ci -> retainedAttackIndices (prune u) `atIx` ci /= Just ci
        _ -> False
      opsWithIndex =
        [ op
        | op <- siteOps
        , any (\(_, o, _, cs, _) -> o == siteOp op && any isIndexed cs) allSites
        ]
  pure $
    conjoin
      ( [ counterexample
            ( opName (siteOp op)
                ++ ": publishes an indexed constituent but yields no"
                ++ " off-diagonal singleton site this property can check — a"
                ++ " transposed mapping would fail open"
            )
            (any (\s@(_, o, _, _, _) -> o == siteOp op && offDiagonal s) indexed)
        | op <- opsWithIndex
        ]
          ++ [ counterexample
                 (base ++ "/" ++ opName op ++ ": published " ++ show predicted)
                 (directionHolds u predicted mutate)
             | (base, op, u, predicted, mutate) <- indexed
             ]
      )
  where
    readAnchorBase base = do
      bytes <- readFile ("examples/" ++ base ++ "/example.core.sexp")
      pure (base, either (const Nothing) Just (decodeCheckInputFile bytes))

    directionHolds u predicted mutate =
      let u' = mutate u
       in case predicted of
            CArgument ci ->
              case soleEdit (unitArgs u) (unitArgs u') of
                Nothing ->
                  counterexample "rewrite did not edit exactly one declared argument" False
                Just di ->
                  counterexample
                    ("rewrite edited declared argument " ++ show di)
                    (retainedIndices (prune u) `atIx` ci === Just di)
            CAttack ci ->
              case soleEdit (unitAttacks u) (unitAttacks u') of
                Nothing ->
                  counterexample "rewrite did not edit or append exactly one attack" False
                Just di
                  -- An in-place rewrite keeps the attack retained, so the base's
                  -- prune maps it; an append is only present in the mutant, so
                  -- the mutant's prune is the one that names its checked index.
                  | di < length (unitAttacks u) ->
                      counterexample
                        ("rewrite edited declared attack " ++ show di)
                        (retainedAttackIndices (prune u) `atIx` ci === Just di)
                  | otherwise ->
                      counterexample
                        ("rewrite appended declared attack " ++ show di)
                        (retainedAttackIndices (prune u') `atIx` ci === Just di)
            _ -> property True

-- | The fixture pins, the argument\/attack siblings of
-- 'prop_conflictSiteQuarantiningBase': on 'quarantiningConflictBase' the
-- enumerators read the checked unit and publish checked indices, mapping only
-- the rewrite back to declared space. @undeclared-leaf@ yields exactly the two
-- retained arguments at @CArgument 0@\/@CArgument 1@ — a declared-space
-- enumerator would publish @1@\/@2@ and offer a third, vanishing site at the
-- pruned @aQ@ — with each rewrite landing on the matching declared argument
-- and @aQ@ untouched. @bad-attack-position@ yields exactly the retained attack
-- at @CAttack 0@ (declared space: @CAttack 1@, plus a vanishing site at the
-- pruned attack), its rewrite landing on declared attack 1. Checker agreement
-- for every site is 'prop_siteMatchesChecker'; this pins the /direction/ of
-- each mapping, so an enumerator inverting both maps cannot cancel to a pass.
prop_sitesQuarantiningBase :: Property
prop_sitesQuarantiningBase =
  once $
    conjoin
      [ counterexample "undeclared-leaf: two sites at checked indices 0 and 1" $
          [cs | (_, cs, _) <- leafSitesQ] === [[CArgument 0], [CArgument 1]]
      , counterexample "undeclared-leaf: rewrites land on declared aS then aK, aQ untouched" $
          [argsAfter m | (_, _, m) <- leafSitesQ]
            === [ [(ArgId "aQ", SLeaf (LeafId "Lq")), (ArgId "aS", mutLeaf), (ArgId "aK", SLeaf (LeafId "Lk"))]
                , [(ArgId "aQ", SLeaf (LeafId "Lq")), (ArgId "aS", SLeaf (LeafId "La")), (ArgId "aK", mutLeaf)]
                ]
      , counterexample "bad-attack-position: one site at checked index 0" $
          [cs | (_, cs, _) <- attackSitesQ] === [[CAttack 0]]
      , counterexample "bad-attack-position: rewrite lands on declared attack 1" $
          [unitAttacks (m u) | (_, _, m) <- attackSitesQ]
            === [ [ Undermine (ArgId "aS") (ArgId "aQ") []
                  , Undermine (ArgId "aS") (ArgId "aK") [StepPremise 99]
                  ]
                ]
      ]
  where
    u = quarantiningConflictBase
    sitesOf op = concat [publishedSites s u | s <- siteOps, siteOp s == op]
    leafSitesQ = sitesOf OpUndeclaredLeaf
    attackSitesQ = sitesOf OpBadAttackPosition
    argsAfter m = unitArgs (m u)
    mutLeaf = SLeaf (LeafId "mut_undeclared")

-- | The localization family's own gate, the composite-list sibling of
-- 'prop_siteMatchesChecker' (which pins every list's /head/ to the checker but
-- cannot see a tail — the checker is fail-fast). Every published element is
-- gated against the /mutant/, on every base the answer key is generated from
-- (anchors, corpus units, the quarantining fixture, and every skewed sibling):
--
--   * @twin-support-defect@ and @cross-stage-defect@ publish a pair, and the
--     tail is derived from the mutant's own bytes: reverting the head defect —
--     restoring the declared argument the published head maps to — must leave a
--     unit the checker rejects at the /tail/ constituent, carrying the tail
--     component's class (@R4@ for twin's second premise defect, @R10@ for
--     cross-stage's attack defect). A composite that publishes a pair but
--     applies only the head rewrite reverts to a clean unit and fails here;
--     one that applies only the tail rewrite fails the sibling arm requiring
--     the head rewrite to have edited that declared argument (and
--     'prop_siteMatchesChecker' besides). This is the review's finding:
--     the previous construction-only clauses re-derived the published lists
--     from the very component enumerators the implementation calls, so
--     dropping the second rewrite left the whole suite green.
--   * the composite lists are /additionally/ pinned to the ordered
--     distinct-constituent pairs of @wrong-premise@'s sites (twin) and the
--     ordered @wrong-premise@ x @bad-attack-position@ cross product
--     (cross-stage). That half catches pair-order, @a \/= b@, and
--     component-class drift; the mutant-derived half above is what makes the
--     tail a real prediction.
--   * @retract-rule@'s published list is re-derived from the /mutant/ alone:
--     in the quarantine-pruned mutated unit, the published arguments are
--     exactly the checked arguments referencing a rule id the mutated policy
--     no longer declares — soundness and completeness of the manifestation
--     set, not a re-run of the enumerator.
--   * where the design fixes an order (twin and retract: ascending checked
--     argument index), the published list is strictly ascending.
--
-- This is also the gate 'prop_siteDirectionSkewed'\'s operator census defers
-- composite-publishing operators to — and that deferral is by the open-ended
-- family string, so the family membership is pinned here: a fourth
-- @localization@ registration fails until this gate covers it. The
-- anti-vacuity half requires each operator to yield a site on a /skewed/
-- base, so the checked-space derivation clauses are exercised off the
-- diagonal, not only where the two index spaces coincide. Since this property
-- is the only gate covering the composite tails, an anchor that fails to
-- decode fails the property outright rather than silently narrowing its
-- coverage (review).
prop_localizationSites :: Property
prop_localizationSites = once $ ioProperty $ do
  corpusBases <- readCorpusBases
  anchors <- mapM readBase mutationBases
  let bases =
        [(b, i) | (b, Right i) <- anchors]
          ++ corpusBases
          ++ [("quarantining-conflict-fixture", testCheckInput quarantiningConflictBase)]
      -- Each base carries its own replay id: the head-revert gate rebuilds a
      -- 'CheckInput' to run the checker, and re-deriving an id would change
      -- the backend and policy the unit is checked under (cf.
      -- 'prop_siteMatchesChecker').
      allBases =
        [(b, inputReplayId i, inputUnit i) | (b, i) <- bases]
          ++ [(b ++ "+skew", inputReplayId i, quarantineSkewed (inputUnit i)) | (b, i) <- bases]
      skewedBases = [(b, u) | (b, _, u) <- allBases, isSkewed u]
      sitesOf op u = concat [publishedSites s u | s <- siteOps, siteOp s == op]
      singles op u = [c | (_, [c], _) <- sitesOf op u]
      ungatedOn op =
        counterexample
          ( "no " ++ opName op ++ " site on any skewed base — the family's"
              ++ " checked-space evidence would be on-diagonal only"
          )
          (any (\(_, u) -> not (null (sitesOf op u))) skewedBases)
  pure $
    conjoin
      ( [ counterexample ("anchor failed to decode: " ++ b ++ ": " ++ show err) (property False)
        | (b, Left err) <- anchors
        ]
          ++ [ counterexample
                 ( "the localization family is exactly the three gated operators —"
                     ++ " a fourth FamLocalization registration must"
                     ++ " extend this gate"
                 )
                 ( sort [siteOp s | s <- siteOps, opFamily (siteOp s) == FamLocalization]
                     === sort [OpRetractRule, OpTwinSupportDefect, OpCrossStageDefect]
                 )
             , ungatedOn OpTwinSupportDefect
             , ungatedOn OpCrossStageDefect
             , ungatedOn OpRetractRule
             ]
          ++ concat
            [ [ counterexample (base ++ ": twin lists are the ordered wrong-premise pairs") $
                  [cs | (_, cs, _) <- sitesOf OpTwinSupportDefect u]
                    === [ [a, b]
                        | a : rest <- tails (singles OpWrongPremise u)
                        , b <- rest
                        , a /= b
                        ]
              , counterexample (base ++ ": cross lists are the ordered premise x attack product") $
                  [cs | (_, cs, _) <- sitesOf OpCrossStageDefect u]
                    === [ [p, a]
                        | p <- singles OpWrongPremise u
                        , a <- singles OpBadAttackPosition u
                        ]
              , conjoin
                  [ tailManifests base rid u R4 cs mutate
                  | (_, cs, mutate) <- sitesOf OpTwinSupportDefect u
                  ]
              , conjoin
                  [ tailManifests base rid u R10 cs mutate
                  | (_, cs, mutate) <- sitesOf OpCrossStageDefect u
                  ]
              , conjoin
                  [ retractManifests base cs (mutate u)
                  | (_, cs, mutate) <- sitesOf OpRetractRule u
                  ]
              , conjoin
                  [ counterexample (base ++ ": " ++ opName op ++ " list not strictly ascending") $
                      strictlyAscendingArgs cs
                  | op <- [OpTwinSupportDefect, OpRetractRule]
                  , (_, cs, _) <- sitesOf op u
                  ]
              ]
            | (base, rid, u) <- allBases
            ]
      )
  where
    -- The composite tail, from the mutant. Both composites publish an
    -- argument-headed pair whose head rewrite edits exactly one declared
    -- argument (the components are 'wrongPremiseSites' proposals). Restoring
    -- that argument in the mutant leaves precisely the tail component's
    -- single-defect mutant, so the checker must reject it at the tail
    -- constituent with the tail component's class — the same prediction
    -- 'prop_siteMatchesChecker' holds that component to, now re-derived
    -- through the composite's own rewrite instead of re-running the
    -- enumerator that produced it.
    tailManifests base rid u tailClass cs mutate = case cs of
      [CArgument ci, tailC] ->
        case retainedIndices (prune u) `atIx` ci of
          Nothing ->
            counterexample
              (base ++ ": published head CArgument " ++ show ci ++ " has no declared index")
              (property False)
          Just di ->
            let m = mutate u
             in case (unitArgs u `atIx` di, unitArgs m `atIx` di) of
                  (Just before, Just after) ->
                    conjoin
                      [ counterexample
                          ( base
                              ++ ": the head rewrite left declared argument "
                              ++ show di
                              ++ " untouched — the composite published a head it did not seed"
                          )
                          (before /= after)
                      , headRevertLocates base rid m di before tailClass tailC
                      ]
                  _ ->
                    counterexample
                      (base ++ ": declared argument " ++ show di ++ " is out of range")
                      (property False)
      _ ->
        counterexample
          (base ++ ": composite published " ++ show cs ++ ", expected an argument-headed pair")
          (property False)

    headRevertLocates base rid m di before tailClass tailC =
      let reverted = m {unitArgs = replaceAt di before (unitArgs m)}
       in case mkCheckInput rid reverted of
            Left err ->
              counterexample
                (base ++ ": head-reverted mutant failed to rebuild: " ++ show err)
                (property False)
            Right input ->
              let (verdict, located) = runCheckLocated input
               in conjoin
                    [ counterexample
                        ( base
                            ++ ": head-reverted mutant produced "
                            ++ show (verdictOutcome verdict)
                            ++ " — the second rewrite is absent from the mutant"
                        )
                        (verdictOutcome verdict === Reject (RejectClass tailClass))
                    , counterexample
                        ( base
                            ++ ": head-reverted mutant located "
                            ++ show (fmap lrConstituent located)
                            ++ ", but the composite publishes tail "
                            ++ show tailC
                        )
                        (fmap lrConstituent located === Just tailC)
                    ]

    replaceAt i x xs = take i xs ++ x : drop (i + 1) xs

    -- Soundness + completeness of the manifestation set, from the mutant: the
    -- published arguments are exactly the checked arguments referencing an
    -- undeclared rule id in the quarantine-pruned mutated unit.
    retractManifests base cs u' =
      let declared = [ruleId r | r <- unitRules u']
          checkedArgs = zip [0 :: Int ..] (map snd (unitArgs (pruneChecked (prune u'))))
          dangling = [CArgument i | (i, t) <- checkedArgs, any (`notElem` declared) (ruleRefs t)]
       in counterexample
            (base ++ ": retract-rule published " ++ show cs ++ ", mutant manifests " ++ show dangling)
            (cs === dangling)
    readBase base = do
      bytes <- readFile ("examples/" ++ base ++ "/example.core.sexp")
      pure (base, decodeCheckInputFile bytes)
    -- A deliberately independent traversal — not Nav's @occurrences@ — so the
    -- oracle cannot inherit a defect from the code under test.
    ruleRefs t = case t of
      SLeaf _ -> []
      SRule rid _ ws d _ _ -> rid : concatMap ruleRefs ws ++ concatMap (ruleRefs . snd) d
    strictlyAscendingArgs cs =
      case mapM argIx cs of
        Just ixs -> and (zipWith (<) ixs (drop 1 ixs))
        Nothing -> False
      where
        argIx (CArgument i) = Just i
        argIx _ = Nothing

-- | The mirror is pinned to the checker: for every site
-- 'dropCoveringAttackSites' proposes, on every base it runs against, the
-- 'Lara.Diagnostics.CConflictPair' it /predicts/ is the one
-- 'Lara.Driver.runCheckLocated' actually reports on the mutated unit.
--
-- This is the property that earns @drop-covering-attack@'s design rationale.
-- Every other check around this operator is strictly weaker:
-- @scripts\/gen-mutants.hs@ and 'prop_specifiedOutcomes' pin the rejection
-- /class/, 'prop_expectedLocationColumn' pins only that the site column is
-- present and round-trips, and 'Lara.Measure.detLocationMatch' does compare
-- located-vs-seeded but flows into @measurements\/report.{json,tsv}@ and is
-- measured, never gated. Without this, a wrong @si@\/@ti@ leaves the whole
-- suite green and silently corrupts the answer key that the localization
-- benchmark consumes — the mutant still rejects with the right class,
-- so nothing else can see it.
prop_conflictSiteMatchesChecker :: Property
prop_conflictSiteMatchesChecker = once $ ioProperty $ do
  corpusBases <- readCorpusBases
  anchors <- mapM readBase mutationBases
  let bases =
        [(b, i) | (b, Just i) <- anchors]
          ++ corpusBases
          ++ [("quarantining-conflict-fixture", testCheckInput quarantiningConflictBase)]
      sites =
        [ (base, input, expected, predicted, mutate)
        | (base, input) <- bases
        , (expected, predicted, mutate) <- dropCoveringAttackSites (inputUnit input)
        ]
  pure $
    conjoin
      ( counterexample
          "no drop-covering-attack sites found — the property would be vacuous"
          (not (null sites))
          : [ counterexample (base ++ ": predicted " ++ show predicted) (agrees site)
            | site@(base, _, _, predicted, _) <- sites
            ]
      )
  where
    readBase base = do
      bytes <- readFile ("examples/" ++ base ++ "/example.core.sexp")
      pure (base, either (const Nothing) Just (decodeCheckInputFile bytes))

    agrees (_, input, expected, predicted, mutate) =
      case mkCheckInput (inputReplayId input) (mutate (inputUnit input)) of
        Left err ->
          counterexample ("mutated unit failed to rebuild: " ++ show err) False
        Right mutated ->
          let (verdict, located) = runCheckLocated mutated
           in conjoin
                [ counterexample "enumerator proposed a non-MissingConflict site" $
                    expected === ExpectMissingConflict
                , counterexample ("outcome was " ++ show (verdictOutcome verdict)) $
                    verdictOutcome verdict === Reject MissingConflict
                , counterexample "checker reported no located rejection" $
                    fmap lrConstituent located === Just predicted
                ]

-- | The @RejectOnConflict@ sibling of 'quarantiningConflictBase'. Same
-- graph, same inconsistent group — only the mode differs, so the driver
-- escalates the group conflict to R9 and rejects before the completeness scan
-- ever runs. Nothing else in the enumerator reads 'unitGroupMode' and the prune
-- is mode-independent, so without the @groupConflictReject@ gate this unit
-- would yield exactly the site its quarantining twin yields, and the mutant
-- would reject R9 rather than @MissingConflict@ — a corrupted answer key for
-- the localization benchmark.
quarantiningConflictRejectBase :: Unit
quarantiningConflictRejectBase =
  quarantiningConflictBase {unitGroupMode = RejectOnConflict}

-- | The result of deleting 'quarantiningConflictBase'\'s /pruned/ attack
-- (declared index 0, the one naming the quarantined @aQ@). The checked unit is
-- unchanged by that deletion, so the unit must still accept — which is why
-- pruned attacks are not candidate sites.
prunedAttackDeletedBase :: Unit
prunedAttackDeletedBase =
  quarantiningConflictBase {unitAttacks = [Undermine (ArgId "aS") (ArgId "aK") []]}

-- | On a quarantining base the enumerator reads the checked unit and maps
-- the deletion back through the prune. Under the fixture's index skew a mirror
-- over the declared unit would publish @(1, 2)@ where the checker reports
-- @(0, 1)@, and a deletion applied in checked index space would remove the
-- pruned attack — an accepting no-op — instead of the cover. Checker agreement
-- for the site itself is asserted by 'prop_conflictSiteMatchesChecker', which
-- carries this fixture as a base.
--
-- Two sibling bases pin the gates the main fixture cannot reach:
-- 'prunedAttackDeletedBase' pins that deleting a /pruned/ attack is an
-- accepting no-op (the length check above is insensitive to it — an enumerator
-- iterating declared attacks would also yield exactly one site here), and
-- 'quarantiningConflictRejectBase' pins the @groupConflictReject@ gate by both
-- its effect (no sites) and its reason (the driver rejects R9 before the
-- scan). No corpus base declares a @groups@ form, so nothing else reaches
-- either path.
prop_conflictSiteQuarantiningBase :: Property
prop_conflictSiteQuarantiningBase =
  once $
    conjoin
      [ counterexample "fixture base must accept" (isAccept (verdictOutcome (runCheck input)))
      , counterexample "exactly one covering attack on the checked unit" (length sites === 1)
      , counterexample "deleting the pruned attack must be an accepting no-op" $
          isAccept (verdictOutcome (runCheck (testCheckInput prunedAttackDeletedBase)))
      , counterexample "an R9-escalating base must yield no sites" $
          null (dropCoveringAttackSites quarantiningConflictRejectBase)
      , counterexample "the R9-escalating base must reject at the driver, not the scan" $
          verdictOutcome (runCheck (testCheckInput quarantiningConflictRejectBase))
            === Reject (RejectClass R9)
      , conjoin
          [ conjoin
              [ counterexample "pair must be published in checked index space" $
                  predicted === CConflictPair 0 1
              , counterexample "deletion must land on the retained declared attack" $
                  unitAttacks (mutate (inputUnit input))
                    === [Undermine (ArgId "aS") (ArgId "aQ") []]
              ]
          | (_, predicted, mutate) <- sites
          ]
      ]
  where
    input = testCheckInput quarantiningConflictBase
    sites = dropCoveringAttackSites (inputUnit input)
    isAccept o = case o of
      Accept{} -> True
      Reject{} -> False

-- | The corpus half of the T1 coverage criterion: every
-- executable rejection class is witnessed by ≥1 corpus-based mutant. All eleven
-- 'RejectClass' values have corpus sites, so all eleven are required (the "where
-- corpus sites exist" hedge is vacuous for this corpus).
prop_corpusCoverage :: Property
prop_corpusCoverage = once $ ioProperty $ do
  rows <- readManifest
  corpusBases <- readCorpusBases
  let corpusLabels = map fst corpusBases
      corpusRows = [r | r <- rows, rowBase r `elem` corpusLabels]
      witnessed = sort (nubOrd [c | Row {rowExpected = ExpectClass c} <- corpusRows])
  pure $
    conjoin
      [ counterexample "no corpus-based mutant rows found" (not (null corpusRows))
      , counterexample
          ("corpus rejection-class coverage incomplete — witnessed " ++ show witnessed)
          (all (`elem` witnessed) [minBound .. maxBound :: RejectClass])
      ]

-- | The corpus sweep budget is honoured with no silent caps: per operator, the
-- selected-base count equals @min(applicable, B = 12)@, and the manifest carries
-- exactly that many corpus rows for the operator. The regenerated README prints
-- the same 'corpusSweepReport', so this ties the manifest, the report, and the
-- budget rule together.
prop_corpusBudget :: Property
prop_corpusBudget = once $ ioProperty $ do
  rows <- readManifest
  corpusBases <- readCorpusBases
  let corpusLabels = map fst corpusBases
      corpusRows = [r | r <- rows, rowBase r `elem` corpusLabels]
      rowsForOp name = length [() | r <- corpusRows, rowOp r == name]
      report = corpusSweepReport corpusBases
  pure $
    conjoin
      [ counterexample
          ( opName op
              ++ ": selected "
              ++ show selected
              ++ " /= min(applicable="
              ++ show applicable
              ++ ", "
              ++ show corpusBudget
              ++ ")"
          )
          (selected === min applicable corpusBudget)
        .&&. counterexample
          ( opName op
              ++ ": manifest has "
              ++ show (rowsForOp (opName op))
              ++ " corpus rows, sweep selected "
              ++ show selected
          )
          (rowsForOp (opName op) === selected)
      | (op, applicable, selected) <- report
      ]

-- | The status of a single-query accept mutant's queried claim (the accept
-- family always constructs single-query units); 'Nothing' on a reject, a codec
-- failure, or a non-single-query accept.
primaryStatus :: String -> Maybe Status
primaryStatus bytes = case decodeCheckInputFile bytes of
  Right input -> case verdictOutcome (runCheck input) of
    Accept _ _ [(_, Published st)] -> Just st
    _ -> Nothing
  Left _ -> Nothing

-- | The status/attack-kind half of the T1 exit criterion: the
-- accept family witnesses every claim status {gap, justified, contested,
-- defeated} and every attack kind {rebut, undercut, undermine} over corpus
-- units. Statuses are read from the @accept-\<status\>@ rows; attack kinds are
-- implied by the accept operator (undercut for attach-undercut/attach-reinstate,
-- undermine for attach-undermine, rebut for attach-rebut-cycle).
prop_statusAttackCoverage :: Property
prop_statusAttackCoverage = once $ ioProperty $ do
  rows <- readManifest
  corpusBases <- readCorpusBases
  let corpusLabels = map fst corpusBases
      corpusRows = [r | r <- rows, rowBase r `elem` corpusLabels]
      statuses = nubOrd [s | Row {rowExpected = ExpectPrimaryStatus s} <- corpusRows]
      attackKinds = nubOrd (concatMap (opAttackKinds . rowOp) corpusRows)
  pure $
    conjoin
      [ counterexample
          ("corpus status coverage incomplete — witnessed " ++ show statuses)
          (all (`elem` statuses) [Gap, Justified, Contested, Defeated])
      , counterexample
          ("corpus attack-kind coverage incomplete — witnessed " ++ show attackKinds)
          (all (`elem` attackKinds) ["rebut", "undercut", "undermine"])
      ]
  where
    opAttackKinds op = case op of
      "attach-undercut" -> ["undercut"]
      "attach-reinstate" -> ["undercut"]
      "attach-undermine" -> ["undermine"]
      "attach-rebut-cycle" -> ["rebut"]
      _ -> []

-- | The 4A structural re-verification (eng review D7): re-deriving the accept
-- family, every mutant satisfies 'acceptStructureOk' — the verdict accepts with
-- the specified primary status AND the operator's constructed label shape (a
-- status-only check passes a no-op reinstate vacuously). This runs the same
-- structural predicate @scripts/gen-mutants.hs@ gates generation on.
prop_acceptStructure :: Property
prop_acceptStructure = once $ ioProperty $ do
  corpusBases <- readCorpusBases
  let mutants = acceptMutants corpusBases
  pure $
    conjoin
      ( counterexample "no accept-family mutants derived" (not (null mutants))
          : [counterexample (mutantName m) (checkOne m) | m <- mutants]
      )
  where
    checkOne m = case (mutantExpected m, decodeCheckInputFile (mutantBytes m)) of
      (expected@(ExpectPrimaryStatus _), Right input) ->
        property (acceptStructureOk (mutantOp m) expected input (runCheck input))
      (ExpectEvidenceBlocked, Right input) ->
        property (acceptStructureOk (mutantOp m) ExpectEvidenceBlocked input (runCheck input))
      (_, Left err) ->
        counterexample ("failed to decode: " ++ show err) (property False)
      _ -> counterexample "not an accept-family mutant" (property False)

nubOrd :: Ord a => [a] -> [a]
nubOrd = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

-- | The @cert-wrong-fraction@ mutant survives the @ra\@1@ decoder and is
-- refused by the /value recheck/; @cert-payload-tamper@ dies in the decoder.
-- That difference is the whole reason the two operators coexist, and no
-- manifest column expresses it: both are @certificate-tampering@, both
-- @reject-R13@, both @arg:0@, and 'codecDiagnostics' is 'Nothing' for both, so
-- the diagnostic columns are empty and @scripts\/differential.sh@ compares
-- stderr only for the codec half.
--
-- Without this property the distinction is unpinned: drop the @(%)@
-- renormalization from 'Lara.Mutate.Sites.Cert.bumpWitness' so the operator
-- emits @(frac 120 500)@, and every other property still passes — 'decodeFrac'
-- rejects it as "not in lowest terms", the outcome is still @reject-R13@, and
-- @prop_seededReproducibility@ simply re-pins the new bytes. The corpus would
-- lose its only witness for the value recheck with nothing turning red.
prop_certWrongFractionDecodes :: Property
prop_certWrongFractionDecodes = once $ ioProperty $ do
  rows <- readManifest
  let rowsFor op = [r | r <- rows, rowOp r == opName op]
      wrongRows = rowsFor OpCertWrongFraction
      -- Contrast on the same base, so the two rows differ only by operator.
      tamperRows =
        [r | r <- rowsFor OpCertPayloadTamper, rowBase r `elem` map rowBase wrongRows]
  wrong <- mapM loadPayloads wrongRows
  tamper <- mapM loadPayloads tamperRows
  pure $
    conjoin
      [ counterexample
          "expected exactly one cert-wrong-fraction row"
          (length wrongRows === 1)
      , counterexample
          "expected a cert-payload-tamper row on the same base to contrast against"
          (not (null tamperRows))
      , conjoin [counterexample (rowPath r) (decodesAndRejects p) | (r, p) <- zip wrongRows wrong]
      , conjoin [counterexample (rowPath r) (failsToDecode p) | (r, p) <- zip tamperRows tamper]
      ]
  where
    loadPayloads row = do
      bytes <- readFile (suiteRoot ++ "/" ++ rowPath row)
      pure $ case decodeCheckInputFile bytes of
        Left _ -> Nothing
        Right input ->
          Just (concatMap (certPayloadsOf . snd) (unitArgs (inputUnit input)), runCheck input)
    decodesAndRejects Nothing =
      counterexample "the mutant did not decode as a check input at all" (property False)
    decodesAndRejects (Just (payloads, verdict)) =
      conjoin
        [ counterexample
            ("expected exactly one certificate payload, got " ++ show (length payloads))
            (length payloads === 1)
        , conjoin
            [ counterexample
                ( "payload must survive the ra@1 decoder — this operator's whole"
                    ++ " point is that it is refused on value, not on grammar; got "
                    ++ show err
                )
                (property False)
            | p <- payloads
            , Left err <- [RA.decodeCert p]
            ]
        , counterexample
            ("expected a reject R13 verdict, got " ++ show (verdictOutcome verdict))
            (verdictOutcome verdict === Reject (RejectClass R13))
        ]
    failsToDecode Nothing = property True -- a codec-boundary mutant; not our contrast
    failsToDecode (Just (payloads, _)) =
      conjoin
        [ counterexample
            "cert-payload-tamper payload decoded cleanly — the two operators have converged"
            (property (isLeftE (RA.decodeCert p)))
        | p <- payloads
        ]
    isLeftE = either (const True) (const False)

-- | Missing a backend's worked-example base used to leave every mutation
-- property green while its certificate rejection paths were absent.
-- Read the measured manifest and replay its actual files, requiring a corrupt
-- certificate for each backend/operator pair rather than just a base name.
prop_backendCertificateCoverage :: Property
prop_backendCertificateCoverage = once $ ioProperty $ do
  rows <- readManifest
  checks <- sequence
    [ checkPair rows base backend op expected
    | (base, backend) <- [("S2", BackendId "ord"), ("S9", BackendId "insp")]
    , (op, expected) <- [(OpCertTheorySwap, R7), (OpCertPayloadTamper, R13)]
    ]
  pure (conjoin checks)
  where
    checkPair rows base backend op expected = do
      let selected = [r | r <- rows, rowBase r == base, rowOp r == opName op]
      checks <- mapM (checkFile backend op expected) selected
      pure $ counterexample (base ++ "/" ++ opName op) $ conjoin
        [ counterexample "no measured certificate mutant" (not (null selected))
        , conjoin checks
        ]
    checkFile backend op expected row = do
      bytes <- readFile (suiteRoot ++ "/" ++ rowPath row)
      pure $ counterexample (rowPath row) $ case decodeCheckInputFile bytes of
        Left err -> counterexample (show err) False
        Right input -> conjoin
          [ rowExpected row === ExpectClass expected
          , verdictOutcome (runCheck input) === Reject (RejectClass expected)
          , counterexample "missing corrupt certificate for the intended backend" $
              any (isTarget backend op)
                (concatMap (certsOf . snd) (unitArgs (inputUnit input)))
          ]
    isTarget backend op c =
      certBackend c == backend && certVersion c == 1
        && case op of
          OpCertTheorySwap -> certTheory c == TheoryDigest "sha256:mut"
          OpCertPayloadTamper -> certPayload c == SAtom "mut_corrupt"
          _ -> False
    certsOf t = case t of
      SLeaf _ -> []
      SRule _ _ ws d _ a ->
        [c | AssuranceCert c <- [a]]
          ++ concatMap certsOf ws ++ concatMap (certsOf . snd) d

-- | Every certificate payload carried anywhere in a support term, in traversal
-- order. Local to this module: "Lara.Mutate.Sites.Nav" is library-internal.
certPayloadsOf :: SupportTerm -> [SExpr]
certPayloadsOf t = case t of
  SLeaf _ -> []
  SRule _ _ ws d _ a ->
    [certPayload c | AssuranceCert c <- [a]]
      ++ concatMap certPayloadsOf ws
      ++ concatMap (certPayloadsOf . snd) d

mutationSpecProps :: [(String, IO Result)]
mutationSpecProps =
  [ ("mutation suite: every mutant produces its specified outcome", quickCheckResult prop_specifiedOutcomes)
  , ("mutation suite: seeded regeneration reproduces committed bytes", quickCheckResult prop_seededReproducibility)
  , ("mutation suite: opFamily is surjective and familyText injective", quickCheckResult prop_familyVocabulary)
  , ("mutation suite: every rejection class, codec negatives, and cycles witnessed", quickCheckResult prop_mutationCoverage)
  , ("mutation suite: Sigma well-formedness and codec clauses have dedicated fixtures", quickCheckResult prop_sigmaFixtureCoverage)
  , ("mutation suite: every rejection class witnessed by a corpus-based mutant", quickCheckResult prop_corpusCoverage)
  , ("mutation suite: corpus sweep budget honoured with no silent caps", quickCheckResult prop_corpusBudget)
  , ("mutation suite: every status and attack kind witnessed by a corpus mutant", quickCheckResult prop_statusAttackCoverage)
  , ("mutation suite: accept family verified structurally (status + label shape)", quickCheckResult prop_acceptStructure)
  , ("mutation suite: runCheck == fst . runCheckLocated over every mutant", quickCheckResult prop_runCheckLocatedConsistent)
  , ("mutation suite: expected-location column round-trips and is present on reject rows", quickCheckResult prop_expectedLocationColumn)
  , ("mutation suite: every proposed site is the constituent the checker reports", quickCheckResult prop_siteMatchesChecker)
  , ("mutation suite: site enumerators map sites through the quarantine prune", quickCheckResult prop_sitesQuarantiningBase)
  , ("mutation suite: published index is checked, rewritten index is declared", quickCheckResult prop_siteDirectionSkewed)
  , ("mutation suite: localization lists decompose to components and the mutant", quickCheckResult prop_localizationSites)
  , ("mutation suite: drop-covering-attack site is the pair the checker reports", quickCheckResult prop_conflictSiteMatchesChecker)
  , ("mutation suite: drop-covering-attack maps sites through the quarantine prune", quickCheckResult prop_conflictSiteQuarantiningBase)
  , ("mutation suite: cert-wrong-fraction decodes cleanly and is refused on value", quickCheckResult prop_certWrongFractionDecodes)
  , ("mutation suite: ord/insp certificate rejection coverage", quickCheckResult prop_backendCertificateCoverage)
  ]
