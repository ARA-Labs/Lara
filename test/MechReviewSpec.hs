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

import Lara.AST (ArgId (..), LeafId (..), QuestionId (..), Status (..), SupportTerm (..))
import Lara.Grounded (Claim (..))
import Lara.MechReview
  ( ReviewComment (..)
  , contestedBody
  , gapBody
  , renderReviews
  , unitReviewComments
  )
import Lara.MechReview.Load (loadReviewUnits)
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.Reporting (ClaimReport (..), IncompleteAlternative (..))

manifestPath, frozenPath :: FilePath
manifestPath = "corpus-units/MANIFEST.tsv"
frozenPath = "measurements/frozen/mechanical-reviews.md"

mechReviewSpecProps :: [(String, IO Result)]
mechReviewSpecProps =
  [ ("mech-review: rendered corpus reviews re-diff the committed frozen golden", quickCheckResult prop_frozenGolden)
  , ("mech-review: one comment per non-justified claim, each naming its diagnostic", quickCheckResult prop_shape)
  , ("mech-review: gap obligation-naming and contested arms render their diagnostic", quickCheckResult prop_uncoveredArms)
  ]

-- | Re-render the whole corpus document from the freshly loaded units and require
-- it to reproduce the COMMITTED @mechanical-reviews.md@ byte-for-byte. This pins
-- every review sentence, the summary counts, and the preamble — the byte-identical
-- re-diff the house freeze discipline applies to generated deliverables.
prop_frozenGolden :: Property
prop_frozenGolden = once $ ioProperty $ do
  units <- loadReviewUnits manifestPath
  frozen <- readFile frozenPath
  pure $ counterexample "frozen mechanical-reviews.md" (renderReviews units === frozen)

-- | The demo's shape invariants over the frozen corpus (48 gap + 3 defeated = 51
-- comments, no justified comment), and that each rendered body carries the
-- diagnostic content its status names: a @defeated@ body names an attacking
-- argument (an @undercut@ \/ @rebut@ \/ @undermine@), a @gap@ body reports the
-- claim as unsupported or names an unmet obligation.
prop_shape :: Property
prop_shape = once $ ioProperty $ do
  units <- loadReviewUnits manifestPath
  let comments = concatMap (\(n, ci, prog) -> unitReviewComments n ci prog) units
      statuses = map (statusWord . rcStatus) comments
      count w = length (filter (== w) statuses)
  pure $
    conjoin
      [ counterexample "total comments" (length comments === 51)
      , counterexample "gap comments" (count "gap" === 48)
      , counterexample "defeated comments" (count "defeated" === 3)
      , counterexample "no justified comment" (count "justified" === 0)
      , counterexample
          "every defeated body names an attacking argument kind"
          (property (all bodyNamesAttack (filter ((== "defeated") . statusWord . rcStatus) comments)))
      , counterexample
          "every gap body reports unsupported or names an obligation"
          (property (all bodyReportsGap (filter ((== "gap") . statusWord . rcStatus) comments)))
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
statusWord :: Status -> String
statusWord s = case s of
  Gap -> "gap"
  Justified -> "justified"
  Contested -> "contested"
  Defeated -> "defeated"
