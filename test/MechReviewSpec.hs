-- | The D2 mechanical-reviewer renderer (#63) as a standing freshness test: the
-- committed golden @measurements\/frozen\/mechanical-reviews.md@ must reproduce
-- byte-for-byte from re-running the pure "Lara.MechReview" renderer over the
-- FROZEN 60 corpus units. If a corpus edit or a checker change moves any per-claim
-- verdict — or the committed document is hand-edited or goes stale — this fails
-- loudly (the freeze discipline the rest of the corpus deliverables use).
--
-- The per-unit IO is loaded through 'Lara.MechReview.Load' — the same loader the
-- renderer (@scripts\/render-reviews.hs@) uses — so the document under test is
-- exactly the document the renderer produces, with no room for the decode\/parse
-- logic to drift between test and script.
--
-- A second property pins the shape invariants the demo rests on: every
-- non-@justified@ claim raises exactly one comment (and no @justified@ claim
-- does), and the review body names the diagnostic content its status implies (a
-- @defeated@ comment names an attacking argument by its kind).
module MechReviewSpec (mechReviewSpecProps) where

import Data.List (isInfixOf)
import Test.QuickCheck

import Lara.AST
  ( ArgId (..)
  , Digest (..)
  , LeafId (..)
  , PolicyId (..)
  , Program (..)
  , QuestionId (..)
  , Status (..)
  , SupportTerm (..)
  )
import qualified Lara.AST as AST
import Lara.Elaborate.Internal (elaborateWithSemanticProgram, registryOf)
import Lara.Grounded (Claim (..))
import Lara.MechReview
  ( ReviewComment (..)
  , contestedBody
  , gapBody
  , renderReviews
  , reviewBody
  , summaryLine
  , unitReviewComments
  )
import Lara.MechReview.Load (loadReviewUnits)
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.Reporting (ClaimReport (..), IncompleteAlternative (..))
import Lara.Syntax (parsePolicy, parseProgram)
import TestReplay (testCheckInput)
import ValueBindingsSpec (boundSource, strictPolicySource, unboundSource)
import Lara.Wire (PublicStatus (..), decodeCheckInputFile, decodeUnit, encodeUnit)

manifestPath, policyPath, frozenPath :: FilePath
manifestPath = "corpus-units/MANIFEST.tsv"
policyPath = "corpus-units/corpus-v1.policy.lara"
frozenPath = "measurements/frozen/mechanical-reviews.md"

mechReviewSpecProps :: [(String, IO Result)]
mechReviewSpecProps =
  [ ("mech-review: rendered corpus reviews re-diff the committed frozen golden", quickCheckResult prop_frozenGolden)
  , ("mech-review: value bindings preserve semantic consumer parity", quickCheckResult prop_valueBindingConsumerParity)
  , ("mech-review: one comment per non-justified claim, each naming its diagnostic", quickCheckResult prop_shape)
  , ("mech-review: gap obligation-naming and contested arms render their diagnostic", quickCheckResult prop_uncoveredArms)
  , ("mech-review: evidence-blocked renders as a nonempty quarantine finding", quickCheckResult prop_evidenceBlocked)
  , ("mech-review: blocked text binds the conditional-status payload", quickCheckResult prop_blockedPayloadBinding)
  , ("mech-review: summary merges hidden conditional labels", quickCheckResult prop_blockedSummary)
  ]

prop_valueBindingConsumerParity :: Property
prop_valueBindingConsumerParity =
  once $
    case (parsePolicy strictPolicySource, parseProgram boundSource, parseProgram unboundSource) of
      (Right policy, Right bound, Right unbound) ->
        case
          ( elaborateWithSemanticProgram (registryOf policy) bound policy
          , elaborateWithSemanticProgram (registryOf policy) unbound policy
          ) of
          (Right (_, _, boundProgram), Right (unboundUnit, _, unboundProgram)) ->
            case decodeUnit (encodeUnit unboundUnit) of
              Left err -> counterexample ("core codec failed: " ++ show err) False
              Right coreUnit ->
                let coreInput = testCheckInput coreUnit
                 in unitReviewComments "value-bindings" coreInput boundProgram
                      === unitReviewComments "value-bindings" coreInput unboundProgram
          values -> counterexample ("elaboration failed: " ++ show values) False
      values -> counterexample ("fixture parse failed: " ++ show values) False


-- | Re-render the whole corpus document from the freshly loaded units and require
-- it to reproduce the COMMITTED @mechanical-reviews.md@ byte-for-byte. This pins
-- every review sentence, the summary counts, and the preamble — the byte-identical
-- re-diff the house freeze discipline applies to generated deliverables.
prop_frozenGolden :: Property
prop_frozenGolden = once $ ioProperty $ do
  units <- loadReviewUnits manifestPath policyPath
  frozen <- readFile frozenPath
  pure $ counterexample "frozen mechanical-reviews.md" (renderReviews units === frozen)

-- | The demo's shape invariants over the frozen corpus (48 gap + 3 defeated = 51
-- comments, no justified comment), and that each rendered body carries the
-- diagnostic content its status names: a @defeated@ body names an attacking
-- argument (an @undercut@ \/ @rebut@ \/ @undermine@), a @gap@ body reports the
-- claim as unsupported or names an unmet obligation.
prop_shape :: Property
prop_shape = once $ ioProperty $ do
  units <- loadReviewUnits manifestPath policyPath
  let comments = concatMap (\(n, ci, prog) -> unitReviewComments n ci prog) units
      statuses = map (publicStatusWord . rcStatus) comments
      count w = length (filter (== w) statuses)
  pure $
    conjoin
      [ counterexample "total comments" (length comments === 51)
      , counterexample "gap comments" (count "gap" === 48)
      , counterexample "defeated comments" (count "defeated" === 3)
      , counterexample "no justified comment" (count "justified" === 0)
      , counterexample
          "every defeated body names an attacking argument kind"
          (property (all bodyNamesAttack (filter ((== "defeated") . publicStatusWord . rcStatus) comments)))
      , counterexample
          "every gap body reports unsupported or names an obligation"
          (property (all bodyReportsGap (filter ((== "gap") . publicStatusWord . rcStatus) comments)))
      ]
  where
    bodyNamesAttack rc =
      any (`isInfixOf` rcBody rc) ["undercut", "rebut", "undermine"]
        && "defeated" `isInfixOf` rcBody rc
    bodyReportsGap rc =
      ("complete-support set is empty" `isInfixOf` rcBody rc
         || "mandatory obligation" `isInfixOf` rcBody rc)
        && "gap" `isInfixOf` rcBody rc

-- | Cover the two phrasing arms the frozen corpus never exercises (all 48 gaps
-- take the no-candidate branch; 0 contested), calling the pure renderers on
-- small hand-built inputs. This exercises 'gapBody's obligation-naming branch
-- (@holes > 0@ — a retained incomplete candidate) in both its singular and
-- plural forms, and the constant 'contestedBody'. Frozen corpus and golden are
-- untouched: these are pure-function unit checks, not corpus rows.
prop_uncoveredArms :: Property
prop_uncoveredArms =
  once $
    conjoin
      [ counterexample "gap: single obligation names it and reads gap" $
          property $
            "the mandatory obligation" `isInfixOf` oneObligation
              && "`external_validity`" `isInfixOf` oneObligation
              && " has no discharging leaf" `isInfixOf` oneObligation
              && "incomplete candidate argument" `isInfixOf` oneObligation
              && "status **gap**." `isInfixOf` oneObligation
      , counterexample "gap: two obligations pluralize and name both" $
          property $
            "`external_validity`" `isInfixOf` twoObligations
              && "`sample_size`" `isInfixOf` twoObligations
              && " have no discharging leaf" `isInfixOf` twoObligations
              && "status **gap**." `isInfixOf` twoObligations
      , counterexample "contested: names the unresolved conflict" $
          property $
            "undec" `isInfixOf` contestedBody
              && "no grounded winner" `isInfixOf` contestedBody
              && "status **contested**." `isInfixOf` contestedBody
      ]
  where
    oneObligation = gapBody (gapReport [QuestionId "external_validity"])
    twoObligations =
      gapBody (gapReport [QuestionId "external_validity", QuestionId "sample_size"])

-- | The exact round-one regression: a conditionally justified blocked claim
-- must survive the justified filter, render an @evidence-blocked@ heading and a
-- nonempty quarantine explanation, while the unaffected justified query stays
-- absent. The frozen corpus has no quarantine, so its golden cannot cover this
-- branch.
prop_evidenceBlocked :: Property
prop_evidenceBlocked = once $ ioProperty $ do
  bytes <- readFile "fixtures/corpus/group-conflict-quarantine-attacker.sexp"
  pure $ case decodeCheckInputFile bytes of
    Left err -> counterexample ("CODEC:" ++ show err) False
    Right input ->
      let comments = unitReviewComments "demo" input reviewProgram
          rendered = renderReviews [("demo", input, reviewProgram)]
       in case comments of
            [rc] ->
              conjoin
                [ counterexample "blocked claim id" (rcClaimId rc === "concl")
                , counterexample "blocked claim presentation binding" (rcClaimNl rc === "blocked claim")
                , counterexample "blocked public status" (rcStatus rc === EvidenceBlocked Justified)
                , counterexample "nonempty quarantine body" $
                    property $
                      not (null (rcBody rc))
                        && "quarantined" `isInfixOf` rcBody rc
                        && "conditional" `isInfixOf` rcBody rc
                , counterexample "public heading" $
                    property ("## demo — evidence-blocked" `isInfixOf` rendered)
                , counterexample "conditional status is not promoted into the heading" $
                    property (not ("## demo — justified" `isInfixOf` rendered))
                , counterexample "unaffected justified query raises no comment" $
                    property (not ("Claim `other`" `isInfixOf` rendered))
                ]
            other -> counterexample ("review comments: " ++ show other) False
  where
    -- Keep this construction positional as an intentional arity witness for the
    -- exported presentation constructor.
    reviewProgram =
      Program
        "demo"
        (Digest "sha256:demo")
        (PolicyId "conformance-v1")
        []
        []
        [AST.DeclClaim (surfaceClaim "concl" "blocked claim"), AST.DeclClaim (surfaceClaim "other" "ordinary claim")]
    surfaceClaim name nl =
      AST.Claim
        { AST.claimId = AST.PropId name
        , AST.claimNl = nl
        , AST.claimFormal = Prop (Pred name) []
        , AST.claimBinding = AST.Binding "review-test" "fixture" AST.Unreviewed
        }

-- | Summary categories are public words, not full 'PublicStatus' values: the
-- hidden conditional labels below must collapse to one @evidence-blocked@
-- bucket.
prop_blockedSummary :: Property
prop_blockedSummary =
  once $
    summaryLine [comment (EvidenceBlocked Justified), comment (EvidenceBlocked Contested)]
      === "**2 review comments** — 2 evidence-blocked."
  where
    comment st =
      ReviewComment
        { rcUnit = "demo"
        , rcClaimId = "concl"
        , rcClaimFormal = "concl"
        , rcClaimNl = ""
        , rcStatus = st
        , rcBody = "blocked"
        }

-- | The conditional label carried by 'EvidenceBlocked' is diagnostic payload,
-- not a hard-coded renderer aside. Exercise all four payload values through
-- the production 'reviewBody' dispatcher so hard-coding its blocked arm is
-- falsified even though the production quarantine fixture currently happens
-- to carry @Justified@.
prop_blockedPayloadBinding :: Property
prop_blockedPayloadBinding =
  once $
    conjoin
      [ counterexample ("conditional payload " ++ statusWord st) $
          property $
            ("would be " ++ statusWord st) `isInfixOf` dispatched st
              && all
                (\other -> other == st || not (("would be " ++ statusWord other) `isInfixOf` dispatched st))
                [Gap, Justified, Contested, Defeated]
      | st <- [Gap, Justified, Contested, Defeated]
      ]
  where
    dispatched st =
      reviewBody Nothing [] [] (const Nothing) (EvidenceBlocked st) (gapReport [])

-- | A minimal @gap@ 'ClaimReport' carrying one incomplete candidate alternative
-- with the given open obligations — the shape 'gapBody's obligation branch reads
-- (only 'crAlternatives' and each alternative's 'iaObligations' are consulted).
gapReport :: [QuestionId] -> ClaimReport
gapReport obligations =
  ClaimReport
    { crQuery = q
    , crClaim = Claim {claimSupport = [], claimHoles = [0]}
    , crStatus = Gap
    , crAlternatives =
        [ IncompleteAlternative
            { iaIndex = 0
            , iaArgId = ArgId "a1"
            , iaTerm = SLeaf (LeafId "e1")
            , iaConclusion = q
            , iaObligations = obligations
            }
        ]
    , crIncompleteAlternative = True
    }
  where
    q = Prop (Pred "supported") [TCon (FunSym "c1") []]

-- | The status word as the summary\/heading spells it (mirrors the renderer's
-- private table; kept here so the shape prop can group by status without
-- exporting the internal speller).
-- | The heading word for a public status, mirroring
-- "Lara.MechReview".@publicStatusWord@ (spec §4.3, issue #76).
publicStatusWord :: PublicStatus -> String
publicStatusWord ps = case ps of
  EvidenceBlocked _ -> "evidence-blocked"
  Published s -> statusWord s

statusWord :: Status -> String
statusWord s = case s of
  Gap -> "gap"
  Justified -> "justified"
  Contested -> "contested"
  Defeated -> "defeated"
