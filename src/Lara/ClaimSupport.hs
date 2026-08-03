-- | Corpus claim-support aggregation (#56): the pure metrics behind
-- @scripts\/claim-support.hs@, a deterministic descriptive pass over the frozen
-- 60 corpus units that emits the four numbers the paper's /Claim-support
-- outcomes/ paragraph cites.
--
-- This is a REPORTING projection of the T3 decode\/run core, not new metatheory
-- (the checker theorems it rests on are already proven): each unit is decoded
-- (@unit.core.sexp@) and run through 'runCheck' for its per-claim 'Status' and
-- the @in@\/@out@ labelling that fixes which arguments are LOAD-BEARING, and its
-- surface source (@unit.lara@, 'Program') supplies the leaf 'Provenance'\/refs
-- and the @challenges(…)@ attack structure the core drops (@unitLeaves@ is only
-- @(LeafId, Prop)@).
--
-- The four numbers (spec: @\\msfive@ in the external paper repo's
-- @evaluation.tex@; this repo ships no @.tex@):
--
--   1. STATUS distribution over the 60 claims
--      (@justified@ \/ @defeated@ \/ @contested@ \/ @gap@).
--   2. LOAD-BEARING LEAVES by provenance: the declared 'Provenance' field (all
--      'AiExecuted' on this corpus — 0 human\/paper-authored, itself a finding)
--      and the 'LeafKind' breakdown (@observed@ \/ @attested@), plus a
--      PAPER-ANCHOR sub-number ('isPaperAnchorRef') counting leaves that
--      additionally cite a direct paper-document locator. (An earlier
--      refs-ORIGIN split — paper-derived vs agent-generated — was abandoned as
--      DEGENERATE: ~96% of refs point into the agent's own artifact, so every
--      load-bearing leaf is agent-produced and the split collapses to 167\/0.)
--   3. DEAD ENDS that produce a valid typed attack: declared 'Attack's whose
--      source is a @challenges(…)@ argument rooted at a leaf carrying an
--      exploration-trace ref (the corpus-native dead-end undercuts), separated
--      from CQ-driven paper-evidence undercuts.
--   4. Fraction of LOAD-BEARING STRICT STEPS carrying a checked certificate.
--      Computed from real rule modes; since #57 the corpus exercises the
--      certificate path (adaptive-pruning\/C04's @rational_drop_recheck@ arg
--      under an @ra\@1@ certificate), so this is 1 \/ 1. The documented
--      @strict_certifier@ population is reported alongside as context.
module Lara.ClaimSupport
  ( -- * Paper anchoring (refs axis of number 2)
    isPaperAnchorRef
  , leafPaperAnchored
    -- * Per-unit record
  , LeafFact (..)
  , UnitRecord (..)
  , computeUnit
    -- * Aggregate
  , ClaimSupportReport (..)
  , aggregate
    -- * Rendering
  , claimSupportJson
  , claimSupportTsv
  , claimSupportTsvHeader
  ) where

import Data.List (nub, sortBy)
import Data.Ord (comparing)

import Data.Char (toLower)

import Lara.AST
  ( Arg (..)
  , ArgConcl (..)
  , ArgId
  , Assurance (..)
  , Attack (..)
  , Decl (..)
  , Label (..)
  , Leaf (..)
  , LeafId (..)
  , LeafKind (..)
  , Mode (..)
  , Program (..)
  , Provenance (..)
  , RuleId
  , SourceRef (..)
  , Status (..)
  , SupportTerm (..)
  , Unit (..)
  )
import Lara.ExpectedJson (JValue (..), renderJson)
import Lara.Measure (EnvBlock (..))
import Lara.Replay (CheckInput (..))
import Lara.SupportTerm (leaves)
import Lara.Wire (Outcome (..), Verdict (..))

-- ---------------------------------------------------------------------------
-- Paper anchoring (the refs axis of number 2)
-- ---------------------------------------------------------------------------

-- Refs in this corpus are ~96% pointers into the AGENT's own artifact files
-- (@logic\/@, @evidence\/@, @trace\/@, @src\/@), so there is no honest
-- "paper-derived vs agent-generated" SPLIT of the leaves — every load-bearing
-- leaf is agent-produced ('AiExecuted'). What IS measurable is how many
-- load-bearing leaves are additionally ANCHORED to a direct locator in the
-- paper's own document, distinguishing a claim grounded in the paper's reported
-- results from one resting only on agent-extracted intermediates.

-- | A direct pointer into the paper's document: a paper experiment locator
-- (@E\<n\>#…@) or a bare structural locator (@Table-…@, @Figure-…@,
-- @Appendix-…@, @Theorem-…@, @Lemma-…@, @Section/section-…@, @paper-…@,
-- @PAPER.…@). Everything else — @logic\/@, @evidence\/@, @trace\/@, @src\/@,
-- @kernel\/@, @*.py@ — is an agent-artifact path, not the paper.
isPaperAnchorRef :: SourceRef -> Bool
isPaperAnchorRef (SourceRef s) =
  hasExperimentHash s || any (`isPrefixCI` s) paperLocatorPrefixes

-- | Whether a leaf carries at least one direct paper-document locator.
leafPaperAnchored :: Leaf -> Bool
leafPaperAnchored = any isPaperAnchorRef . leafRefs

paperLocatorPrefixes :: [String]
paperLocatorPrefixes =
  [ "table"
  , "figure"
  , "appendix"
  , "theorem"
  , "lemma"
  , "corollary"
  , "proposition"
  , "equation"
  , "section"
  , "paper"
  ]

-- | @E@ followed by one or more digits then @#@ anywhere in the ref (a paper
-- experiment section pointer, e.g. @E01#Table-2@).
hasExperimentHash :: String -> Bool
hasExperimentHash [] = False
hasExperimentHash ('E' : rest@(d : _))
  | isDigit d, ('#' : _) <- dropWhile isDigit rest = True
hasExperimentHash (_ : rest) = hasExperimentHash rest

isDigit :: Char -> Bool
isDigit c = c >= '0' && c <= '9'

isPrefixCI :: String -> String -> Bool
isPrefixCI [] _ = True
isPrefixCI _ [] = False
isPrefixCI (a : as) (b : bs) = toLower a == toLower b && isPrefixCI as bs

-- ---------------------------------------------------------------------------
-- Per-unit record
-- ---------------------------------------------------------------------------

-- | One leaf's reported attributes (number 2): its declared 'Provenance', its
-- 'LeafKind', and whether it is anchored to a direct paper-document locator.
data LeafFact = LeafFact
  { lfId :: LeafId
  , lfProvenance :: Provenance
  , lfKind :: LeafKind
  , lfPaperAnchored :: Bool
  }
  deriving (Eq, Show)

-- | Everything one corpus unit contributes to the four numbers.
data UnitRecord = UnitRecord
  { urName :: String
  , urStatuses :: [Status] -- ^ per requested claim (corpus units: one)
  , urLoadBearing :: [LeafFact] -- ^ leaves of @in@-labelled support args (number 2)
  , urAllLeaves :: [LeafFact] -- ^ every declared leaf (context)
  , urTypedAttacks :: Int -- ^ declared typed attacks, all valid on accept (number 3)
  , urDeadEndAttacks :: Int -- ^ subset sourced at an exploration dead end (number 3)
  , urStrictSteps :: Int -- ^ load-bearing strict steps (number 4 denominator)
  , urStrictCertified :: Int -- ^ …carrying a checked certificate (number 4 numerator)
  , urStrictFlavored :: Bool -- ^ documented @strict_certifier@ header (context; set by IO)
  }
  deriving (Eq, Show)

-- | Compute one unit's contribution. @ruleModeOf@ resolves a support term's
-- 'RuleId' to its policy 'Mode' (built once from the shared policy); @flavored@
-- is the documented @strict_certifier@ header flag; @ci@\/@verdict@ are the T3
-- decode + 'runCheck' outputs; @prog@ is the parsed @unit.lara@ surface.
--
-- A non-accept verdict is a hard error: every frozen corpus unit is
-- accept-class, so a reject means the freeze or the decode path drifted.
computeUnit
  :: (RuleId -> Mode)
  -> Bool
  -> String
  -> CheckInput
  -> Verdict
  -> Program
  -> UnitRecord
computeUnit ruleModeOf flavored name ci (Verdict _ outcome) prog =
  case outcome of
    Reject _ -> error ("claim-support: non-accept corpus unit " ++ name)
    Accept labels _ statuses ->
      UnitRecord
        { urName = name
        , urStatuses = map snd statuses
        , urLoadBearing = map leafFact loadBearingLeafIds
        , urAllLeaves = map leafFactFromLeaf surfaceLeaves
        , urTypedAttacks = length attacks
        , urDeadEndAttacks = length (filter deadEndSourced attacks)
        , urStrictSteps = length (filter (isStrict . snd) loadBearingArgs)
        , urStrictCertified =
            length (filter (\(_, t) -> isStrict t && isCertified t) loadBearingArgs)
        , urStrictFlavored = flavored
        }
      where
        unit = inputUnit ci
        indexedArgs = zip [0 :: Int ..] (unitArgs unit)
        loadBearingArgs =
          [ pair
          | (i, pair) <- indexedArgs
          , lookup i labels == Just LIn
          ]
        loadBearingLeafIds = nub (concatMap (leaves . snd) loadBearingArgs)

        surfaceLeaves = [l | DeclLeaf l <- programDecls prog]
        surfaceArgs = [a | DeclArg a <- programDecls prog]
        leafById lid = lookup lid [(leafId l, l) | l <- surfaceLeaves]

        leafFactFromLeaf l =
          LeafFact (leafId l) (leafProvenance l) (leafKind l) (leafPaperAnchored l)
        -- A load-bearing core leaf id with no surface declaration means the core
        -- and the @.lara@ surface have drifted apart; hard-error rather than
        -- fabricate a leaf fact (mirrors the non-accept 'Reject' arm above).
        leafFact lid = case leafById lid of
          Just l -> leafFactFromLeaf l
          Nothing ->
            error
              ( "claim-support: core leaf " ++ show lid
                  ++ " missing from surface decls in unit " ++ name
              )

        attacks = unitAttacks unit
        argById aid = lookup aid [(argId a, a) | a <- surfaceArgs]
        -- A dead-end attack: its source argument is a @challenges(…)@ whose
        -- rooted leaf carries an exploration-trace ref. This separates the
        -- corpus-native dead-end undercuts from CQ-driven paper-evidence
        -- undercuts (whose leaf refs are paper tables, e.g. fre C04). A missing
        -- source arg or a source leaf absent from the surface is drift, not a
        -- non-dead-end: hard-error rather than silently drop the attack.
        deadEndSourced atk = case argById (attackSrc atk) of
          Just a | isChallenge (argConcl a) ->
            any leafHasTraceRef (leaves (argTerm a))
          Just _ -> False
          Nothing ->
            error
              ( "claim-support: attack source arg " ++ show (attackSrc atk)
                  ++ " missing from surface decls in unit " ++ name
              )
        leafHasTraceRef lid = case leafById lid of
          Just l -> any isTraceRef (leafRefs l)
          Nothing ->
            error
              ( "claim-support: dead-end source leaf " ++ show lid
                  ++ " missing from surface decls in unit " ++ name
              )

        isStrict t = case t of
          SRule {srRule = r} -> ruleModeOf r == Strict
          _ -> False
        isCertified t = case t of
          SRule {srAssurance = AssuranceCert _} -> True
          _ -> False

attackSrc :: Attack -> ArgId
attackSrc (Rebut s _) = s
attackSrc (Undercut s _ _) = s
attackSrc (Undermine s _ _) = s

isChallenge :: ArgConcl -> Bool
isChallenge (Challenges _) = True
isChallenge _ = False

-- | A ref into the agent's exploration trace (@trace\/…@ / @exploration_tree@) —
-- the dead-end signal for number 3, distinguishing an exploration-dead-end
-- undercut from a CQ-driven paper-evidence undercut.
isTraceRef :: SourceRef -> Bool
isTraceRef (SourceRef s) = substr "trace/" s || substr "exploration_tree" s

substr :: String -> String -> Bool
substr needle hay = any (needle `isPrefixList`) (tailsList hay)
  where
    isPrefixList [] _ = True
    isPrefixList _ [] = False
    isPrefixList (a : as) (b : bs) = a == b && isPrefixList as bs
    tailsList [] = [[]]
    tailsList xs@(_ : rest) = xs : tailsList rest

-- ---------------------------------------------------------------------------
-- Aggregate
-- ---------------------------------------------------------------------------

-- | The corpus-wide roll-up of every 'UnitRecord' — the four numbers.
data ClaimSupportReport = ClaimSupportReport
  { csUnits :: Int
  , csStatus :: [(Status, Int)] -- ^ number 1
  , csLoadBearingTotal :: Int -- ^ number 2 denominator
  , csLoadBearingProvenance :: [(Provenance, Int)] -- ^ number 2 (provenance-field axis)
  , csLoadBearingKind :: [(LeafKind, Int)] -- ^ number 2 (observed/attested axis)
  , csLoadBearingPaperAnchored :: Int -- ^ number 2 (paper-anchor sub-number)
  , csAllTotal :: Int -- ^ context
  , csAllProvenance :: [(Provenance, Int)]
  , csAllKind :: [(LeafKind, Int)]
  , csAllPaperAnchored :: Int
  , csTypedAttacks :: Int -- ^ number 3 (total valid)
  , csDeadEndAttacks :: Int -- ^ number 3 (dead-end-sourced subset)
  , csStrictSteps :: Int -- ^ number 4 denominator
  , csStrictCertified :: Int -- ^ number 4 numerator
  , csStrictFlavored :: Int -- ^ documented strict-flavored population (context)
  }
  deriving (Eq, Show)

aggregate :: [UnitRecord] -> ClaimSupportReport
aggregate recs =
  ClaimSupportReport
    { csUnits = length recs
    , csStatus = tally allStatuses
    , csLoadBearingTotal = length lbLeaves
    , csLoadBearingProvenance = tally (map lfProvenance lbLeaves)
    , csLoadBearingKind = tally (map lfKind lbLeaves)
    , csLoadBearingPaperAnchored = length (filter lfPaperAnchored lbLeaves)
    , csAllTotal = length allLeaves
    , csAllProvenance = tally (map lfProvenance allLeaves)
    , csAllKind = tally (map lfKind allLeaves)
    , csAllPaperAnchored = length (filter lfPaperAnchored allLeaves)
    , csTypedAttacks = sum (map urTypedAttacks recs)
    , csDeadEndAttacks = sum (map urDeadEndAttacks recs)
    , csStrictSteps = sum (map urStrictSteps recs)
    , csStrictCertified = sum (map urStrictCertified recs)
    , csStrictFlavored = length (filter urStrictFlavored recs)
    }
  where
    allStatuses = concatMap urStatuses recs
    lbLeaves = concatMap urLoadBearing recs
    allLeaves = concatMap urAllLeaves recs

-- | Count occurrences, most-frequent first (ties by 'show' for determinism).
tally :: (Eq a, Ord a, Show a) => [a] -> [(a, Int)]
tally xs =
  sortBy (comparing (negate . snd) <> comparing (show . fst))
    [(k, length (filter (== k) xs)) | k <- nub' xs]
  where
    nub' = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

-- ---------------------------------------------------------------------------
-- Rendering (house JValue codec; and flat per-unit TSV)
-- ---------------------------------------------------------------------------

claimSupportJson :: EnvBlock -> ClaimSupportReport -> [UnitRecord] -> String
claimSupportJson env rep recs =
  renderJson $
    JObject
      [ ("environment", envJson env)
      , ("corpus", JObject [("frozen-tag", JString "m5-freeze-v2"), ("seed", JNumber 20260801), ("units", JNumber (csUnits rep))])
      , ("status-distribution", JObject (map statusCell (csStatus rep)))
      , ( "load-bearing-leaves"
        , JObject
            [ ("total", JNumber (csLoadBearingTotal rep))
            , ("provenance", JObject (map provCell (csLoadBearingProvenance rep)))
            , ("kind", JObject (map kindCell (csLoadBearingKind rep)))
            , ("paper-anchored", JNumber (csLoadBearingPaperAnchored rep))
            , ("note", JString "All load-bearing leaves are agent-produced (provenance ai-executed); none human/paper-authored. `paper-anchored` counts those additionally citing a direct paper-document locator (an E<n># experiment pointer, or a Table/Figure/Appendix/Theorem/Lemma/Corollary/Proposition/Equation/Section/paper locator).")
            ]
        )
      , ( "all-leaves"
        , JObject
            [ ("total", JNumber (csAllTotal rep))
            , ("provenance", JObject (map provCell (csAllProvenance rep)))
            , ("kind", JObject (map kindCell (csAllKind rep)))
            , ("paper-anchored", JNumber (csAllPaperAnchored rep))
            ]
        )
      , ( "dead-end-attacks"
        , JObject
            [ ("typed-attacks-total", JNumber (csTypedAttacks rep))
            , ("dead-end-sourced", JNumber (csDeadEndAttacks rep))
            ]
        )
      , ( "strict-certificates"
        , JObject
            [ ("load-bearing-strict-steps", JNumber (csStrictSteps rep))
            , ("carrying-checked-certificate", JNumber (csStrictCertified rep))
            , ("documented-strict-flavored", JNumber (csStrictFlavored rep))
            , ("note", JString "The certificate path is exercised since #57: adaptive-pruning/C04's derived-arithmetic leg is a strict rational_drop_recheck step under a checked ra@1 certificate. The remaining documented strict-flavored claims await their own certifier backends.")
            ]
        )
      , ("units", JArray (map unitJson recs))
      ]

statusCell :: (Status, Int) -> (String, JValue)
statusCell (s, n) = (statusStr s, JNumber n)

provCell :: (Provenance, Int) -> (String, JValue)
provCell (p, n) = (provStr p, JNumber n)

kindCell :: (LeafKind, Int) -> (String, JValue)
kindCell (k, n) = (kindStr k, JNumber n)

unitJson :: UnitRecord -> JValue
unitJson r =
  JObject
    [ ("unit", JString (urName r))
    , ("status", JArray (map (JString . statusStr) (urStatuses r)))
    , ("load-bearing-leaves", JNumber (length (urLoadBearing r)))
    , ("load-bearing-paper-anchored", JNumber (countAnchored (urLoadBearing r)))
    , ("typed-attacks", JNumber (urTypedAttacks r))
    , ("dead-end-attacks", JNumber (urDeadEndAttacks r))
    , ("strict-steps", JNumber (urStrictSteps r))
    , ("strict-certified", JNumber (urStrictCertified r))
    ]

countAnchored :: [LeafFact] -> Int
countAnchored = length . filter lfPaperAnchored

envJson :: EnvBlock -> JValue
envJson env =
  JObject
    [ ("git-rev", JString (envGitRev env))
    , ("git-dirty", JBool (envGitDirty env))
    , ("ghc", JString (envGhc env))
    , ("lean", JString (envLean env))
    , ("os", JString (envOs env))
    , ("cpu", JString (envCpu env))
    ]

-- | Flat per-unit TSV (the table-generator input).
claimSupportTsvHeader :: String
claimSupportTsvHeader =
  intercalateTab
    [ "unit"
    , "status"
    , "load_bearing_leaves"
    , "lb_paper_anchored"
    , "typed_attacks"
    , "dead_end_attacks"
    , "strict_steps"
    , "strict_certified"
    , "strict_flavored"
    ]

claimSupportTsv :: [UnitRecord] -> String
claimSupportTsv recs = unlines (claimSupportTsvHeader : map row recs)
  where
    row r =
      intercalateTab
        [ urName r
        , unwordsBar (map statusStr (urStatuses r))
        , show (length (urLoadBearing r))
        , show (countAnchored (urLoadBearing r))
        , show (urTypedAttacks r)
        , show (urDeadEndAttacks r)
        , show (urStrictSteps r)
        , show (urStrictCertified r)
        , if urStrictFlavored r then "yes" else "no"
        ]

unwordsBar :: [String] -> String
unwordsBar [] = "-"
unwordsBar xs = foldr1 (\a b -> a ++ "|" ++ b) xs

intercalateTab :: [String] -> String
intercalateTab [] = ""
intercalateTab [x] = x
intercalateTab (x : xs) = x ++ "\t" ++ intercalateTab xs

statusStr :: Status -> String
statusStr Gap = "gap"
statusStr Justified = "justified"
statusStr Contested = "contested"
statusStr Defeated = "defeated"

provStr :: Provenance -> String
provStr User = "user"
provStr AiExecuted = "ai-executed"
provStr (Checker n v) = "checker(" ++ n ++ "," ++ v ++ ")"

kindStr :: LeafKind -> String
kindStr Observed = "observed"
kindStr Attested = "attested"
kindStr Assumed = "assumed"
kindStr Certified = "certified"
