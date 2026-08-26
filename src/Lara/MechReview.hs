-- | D2 — mechanical reviewer (#63): render the checker's own per-claim verdicts
-- over the FROZEN 60-unit corpus as reviewer-style markdown \"review comments\".
--
-- This is __untrusted presentation__ over the existing accept-path diagnostics —
-- no LLM, no new trusted code. Each non-@justified@ claim yields one review
-- comment whose text is a deterministic function of the checker's located
-- diagnostic (the per-claim 'PublicStatus', the grounded argument labels, the declared
-- typed attacks, and — for a @gap@ with an incomplete candidate — the open
-- mandatory obligations "Lara.Reporting" reports). The point the demo makes for
-- the paper: the status the checker computes __is__ the review content. A @gap@
-- with its named unmet obligation reads as the reviewer complaint it corresponds
-- to; a @defeated@ verdict names the attacking argument that sinks the claim.
--
-- The verdict, labels, and statuses are taken verbatim from the real pipeline
-- ("Lara.Driver".'runCheck'), exactly as "Lara.ExpectedJson" does, so the
-- rendered review can never disagree with the wire verdict. The obligation
-- naming for the @gap@-with-incomplete-alternative shape reuses
-- "Lara.Reporting".'claimReports' (the same lenient scan @expected.json@ uses).
--
-- __Determinism__ is the whole point (goldenable): a FIXED phrasing table keyed
-- on the diagnostic shape, fixed manifest ordering, no timestamps, no
-- environment block. Re-running the renderer reproduces the committed bytes
-- (@test\/MechReviewSpec.hs@).
module Lara.MechReview
  ( -- * Per-claim review comments
    ReviewComment (..)
  , unitReviewComments
    -- * The rendered corpus document
  , renderReviews
  , summaryLine
    -- * Pure phrasing renderers (exposed for focused test coverage)
  , reviewBody
  , gapBody
  , contestedBody
  , evidenceBlockedBody
  ) where

import Data.List (intercalate, nub, sortBy)
import Data.Ord (comparing)

import Lara.AST
  ( Arg (..)
  , ArgConcl (..)
  , ArgId (..)
  , Attack (..)
  , ChallengeTarget (..)
  , Claim (..)
  , Decl (..)
  , Label (..)
  , LeafId (..)
  , Program (..)
  , PropId (..)
  , QuestionId (..)
  , Status (..)
  , Unit (..)
  )
import Lara.Driver (buildCertOk, buildGamma, runCheck)
import Lara.Policy (lookupRule)
import Lara.Prop (equiv, prettyProp)
import Lara.Replay (CheckInput, inputUnit)
import Lara.Reporting (ClaimReport (..), IncompleteAlternative (..), claimReports)
import Lara.Wire
  ( Outcome (..)
  , PublicStatus (..)
  , Tag (TEvidenceBlocked)
  , Verdict (..)
  , tagToString
  )

-- ---------------------------------------------------------------------------
-- Per-claim review comments
-- ---------------------------------------------------------------------------

-- | One reviewer-style comment about a single non-@justified@ public claim: the
-- unit it belongs to, the claim's surface id + formal proposition +
-- natural-language statement, its 'PublicStatus', and the deterministic review
-- body.
data ReviewComment = ReviewComment
  { rcUnit :: String -- ^ manifest unit name (@artifact.claim@)
  , rcClaimId :: String -- ^ the surface claim id (e.g. @c03@)
  , rcClaimFormal :: String -- ^ 'prettyProp' of the claim atom
  , rcClaimNl :: String -- ^ the claim's natural-language statement
  , rcStatus :: PublicStatus
  -- ^ the public status: 'Published' carries the four-state answer,
  -- 'EvidenceBlocked' the conditional label a §4.3 prune made unpublishable
  -- (issue #76). The heading and the body both read this, so a rendered review
  -- can never disagree with the wire verdict.
  , rcBody :: String -- ^ the fixed-phrasing review sentence(s)
  }
  deriving (Eq, Show)

-- | The declaration-order view of a surface argument: its index (which is also
-- its grounded-label index), its id, and its declared conclusion.
data ArgView = ArgView
  { avIndex :: Int
  , avId :: String
  , avConcl :: ArgConcl
  }

-- | The review comments for one corpus unit: one per non-@justified@ requested
-- claim, in claim (query) order. A @justified@ claim raises no comment. The
-- verdict is taken from "Lara.Driver".'runCheck' (identical to the wire verdict);
-- @name@ is the manifest unit name; @prog@ is the parsed @unit.lara@ surface
-- (the only place the author's @supports@\/@challenges@ conclusions live — the
-- checker 'Unit' keeps arguments as bare @(ArgId, SupportTerm)@).
unitReviewComments :: String -> CheckInput -> Program -> [ReviewComment]
unitReviewComments name ci prog =
  case verdictOutcome (runCheck ci) of
    Reject _ -> [] -- every frozen corpus unit is accept-class; nothing to render
    -- An @evidence-blocked@ query is not a justified claim whatever its
    -- conditional label says (spec §4.3, issue #76), so it still draws a comment.
    Accept labels _edges statuses ->
      [ comment p st rep
      | ((p, st), rep) <- zip statuses reports
      , st /= Published Justified
      ]
      where
        unit = inputUnit ci
        gamma = buildGamma (unitLeaves unit)
        certOk = buildCertOk (unitTheories unit)
        pI = lookupRule (unitRules unit)
        reports = claimReports pI gamma certOk unit

        argViews =
          [ ArgView i aid (argConcl a)
          | (i, a) <- zip [0 ..] [x | DeclArg x <- programDecls prog]
          , let ArgId aid = argId a
          ]
        surfaceClaims = [c | DeclClaim c <- programDecls prog]
        attacks = unitAttacks unit
        labelOf i = lookup i labels

        comment p st rep =
          ReviewComment
            { rcUnit = name
            , rcClaimId = claimIdText p
            , rcClaimFormal = prettyProp p
            , rcClaimNl = claimNlText p
            , rcStatus = st
            , rcBody = reviewBody (claimId <$> matchingClaim p) argViews attacks labelOf st rep
            -- 'reviewBody' reads the public status, so the blocked case cannot
            -- fall through to the four-state arms.
            }

        matchingClaim p = case [c | c <- surfaceClaims, equiv (claimFormal c) p] of
          (c : _) -> Just c
          [] -> Nothing
        claimIdText p =
          maybe (prettyProp p) (\c -> let PropId i = claimId c in i) (matchingClaim p)
        claimNlText p = maybe "" claimNl (matchingClaim p)

-- ---------------------------------------------------------------------------
-- Fixed phrasing table (keyed on diagnostic shape)
-- ---------------------------------------------------------------------------

-- | The deterministic review sentence for one non-@justified@ public claim,
-- dispatched on its 'PublicStatus'. Each arm is a fixed template filled from
-- the checker's located diagnostic; the wording is byte-stable so the corpus
-- document goldens.
reviewBody
  :: Maybe PropId -- ^ the declared claim id under review (scopes @defeated@ supports)
  -> [ArgView]
  -> [Attack]
  -> (Int -> Maybe Label)
  -> PublicStatus
  -> ClaimReport
  -> String
reviewBody claimPid argViews attacks labelOf status rep = case status of
  -- Spec §4.3 / issue #76: the four-state label under an @evidence-blocked@
  -- claim is a conditional diagnostic, so the body names the quarantine rather
  -- than reporting the label as the finding.
  EvidenceBlocked conditional -> evidenceBlockedBody conditional
  Published Gap -> gapBody rep
  Published Defeated -> defeatedBody claimPid argViews attacks labelOf
  Published Contested -> contestedBody
  Published Justified -> "" -- unreachable: 'unitReviewComments' filters justified claims

-- | @gap@: the mandatory obligation left open, or — when the claim has no
-- candidate argument at all — the empty complete-support set. The obligation
-- naming fires when "Lara.Reporting" retained an incomplete candidate alternative
-- (a support term that type-checks but leaves a mandatory critical question open,
-- spec §6.1); otherwise the claim is stated with no assembling argument and the
-- gap is total.
gapBody :: ClaimReport -> String
gapBody rep = case obligations of
  (o : os) ->
    "the mandatory obligation "
      ++ commaList (map tick (o : os))
      ++ (if null os then " has" else " have")
      ++ " no discharging leaf: an incomplete candidate argument for this claim"
      ++ " leaves "
      ++ (if null os then "it" else "them")
      ++ " open, so no complete argument supports the claim — status **gap**."
  [] ->
    "no argument assembles the unit's evidence into a checked support for this"
      ++ " claim; its complete-support set is empty, so at the `corpus-v1`"
      ++ " evidential bar the claim is unsupported — status **gap**."
  where
    obligations =
      nub [q | alt <- crAlternatives rep, QuestionId q <- iaObligations alt]

-- | @defeated@: the claim's support argument(s) labelled @out@, each with the
-- winning (@in@) attacker that sinks it — named by its kind (rebut \/ undercut \/
-- undermine) and, for a @challenges(…)@ argument, what it challenges.
defeatedBody :: Maybe PropId -> [ArgView] -> [Attack] -> (Int -> Maybe Label) -> String
defeatedBody claimPid argViews attacks labelOf =
  case outSupport of
    [] ->
      "the claim's support is defeated in the grounded labelling — status"
        ++ " **defeated**."
    _ ->
      "the claim's "
        ++ (if singleSupport then "only support " else "support ")
        ++ commaList (map tick outSupport)
        ++ (if singleSupport then " is" else " are")
        ++ " labelled `out`: "
        ++ commaList (concatMap defeaterClauses outSupport)
        ++ " — status **defeated**."
  where
    -- Support arguments for THIS claim, by surface id: an @arg … : supports(c)@
    -- whose declared claim id is the one under review. Scoping to the claim keeps
    -- a multi-claim unit from naming another claim's @out@ support. With no
    -- matching declared claim id (should not happen for a declared claim), fall
    -- back to every declared @supports(…)@ argument.
    supportIds =
      [ avId a | a <- argViews, supportsThisClaim (avConcl a) ]
    supportsThisClaim concl = case claimPid of
      Just pid -> concl == SupportsClaim pid
      Nothing -> isSupportsClaim concl
    outSupport = [i | i <- supportIds, labelOfId i == Just LOut]
    singleSupport = length outSupport == 1

    -- The winning (in) attackers of one out-labelled support argument, each with
    -- its actual standing in the labelling ('standing').
    defeaterClauses tgtId =
      [ "the "
          ++ attackKind atk
          ++ " "
          ++ tick srcId
          ++ challengeClause srcId
          ++ standing srcId
          ++ " and defeats "
          ++ tick tgtId
      | atk <- attacks
      , let (srcId, atkTgt) = attackEndpoints atk
      , atkTgt == tgtId
      , labelOfId srcId == Just LIn
      ]

    -- Why the @in@ attacker stands. It is only NECESSARILY unattacked in the
    -- degenerate case; in general a grounded-@in@ node may be attacked but
    -- defended (all of its own attackers labelled @out@). Read the actual
    -- incoming attacks from the attack set rather than asserting "unattacked".
    standing srcId
      | hasIncomingAttack srcId =
          " is itself undefeated (its attackers are all labelled `out`)"
      | otherwise = " is unattacked"
    hasIncomingAttack s = any ((== s) . snd . attackEndpoints) attacks

    challengeClause srcId = case conclById srcId of
      Just (Challenges (ChallengesQuestion (QuestionId q) (ArgId u))) ->
        " (challenging the " ++ tick q ++ " critical question of " ++ tick u ++ ")"
      Just (Challenges (ChallengesLeaf (LeafId l))) ->
        " (challenging evidence leaf " ++ tick l ++ ")"
      _ -> ""

    labelOfId i = indexOfId i >>= labelOf
    indexOfId i = lookup i [(avId a, avIndex a) | a <- argViews]
    conclById i = lookup i [(avId a, avConcl a) | a <- argViews]

-- | @contested@: the claim's support is caught in an unresolved conflict — the
-- @undec@-labelled arguments that attack each other with no grounded winner.
contestedBody :: String
contestedBody =
  "the claim's support is caught in an unresolved conflict: the arguments"
    ++ " attack each other with no grounded winner (labelled `undec`), so the"
    ++ " status is neither in nor out — status **contested**."

-- ---------------------------------------------------------------------------
-- The rendered corpus document
-- ---------------------------------------------------------------------------

-- | The full mechanical-review document over the corpus units (in the supplied
-- order — manifest order at the call site). A fixed preamble, a derived summary
-- line, then one section per review comment. Ends with a single trailing
-- newline; byte-stable (no timestamps, no environment).
renderReviews :: [(String, CheckInput, Program)] -> String
renderReviews units =
  unlines $
    preamble
      ++ [summaryLine comments, ""]
      ++ concatMap section comments
  where
    comments = concatMap (\(n, ci, prog) -> unitReviewComments n ci prog) units

-- | The fixed document header (identical on every run).
preamble :: [String]
preamble =
  [ "# Mechanical reviewer — corpus claim-support verdicts as reviews"
  , ""
  , "Deterministically generated by `scripts/render-reviews.hs` from the checker's"
  , "own per-claim verdicts over the frozen 60-unit corpus sample"
  , "(`corpus-units/MANIFEST.tsv`, seed 20260801). NOT an LLM,"
  , "and no new trusted code: this is untrusted presentation over the accept-path"
  , "located diagnostics (`Lara.MechReview`). One review comment per"
  , "non-`justified` claim, in manifest order; a `justified` claim raises no"
  , "comment. The status the checker computes IS the review content — a `gap` names"
  , "its unmet obligation (or empty support), a `defeated` names the attacking"
  , "argument that sinks the claim, a `contested` names the unresolved conflict."
  , ""
  ]

-- | The derived one-line summary (counts recomputed from the comments, so it
-- stays fresh with the corpus).
summaryLine :: [ReviewComment] -> String
summaryLine comments =
  "**"
    ++ show (length comments)
    ++ " review comments** — "
    ++ commaList
      [ show n ++ " " ++ w
      | (w, n) <- statusTally (map rcStatus comments)
      ]
    ++ "."

-- | One rendered review section for a single comment.
section :: ReviewComment -> [String]
section rc =
  [ "## " ++ rcUnit rc ++ " — " ++ publicStatusWord (rcStatus rc)
  , ""
  , "Claim `" ++ rcClaimId rc ++ "`: `" ++ rcClaimFormal rc ++ "`"
  ]
    ++ nlBlock
    ++ [ ""
       , "> " ++ upcaseFirst (rcBody rc)
       , ""
       ]
  where
    nlBlock
      | null (rcClaimNl rc) = []
      | otherwise = ["", "*Stated:* " ++ rcClaimNl rc]

-- ---------------------------------------------------------------------------
-- Small deterministic helpers (closed spelling tables; no external deps)
-- ---------------------------------------------------------------------------

-- | The reviewer sentence for an @evidence-blocked@ claim (spec §4.3, issue
-- #76): the claim's own graph was edited by quarantine, so no four-state
-- finding can be reported — and the conditional label is named as such rather
-- than published.
evidenceBlockedBody :: Status -> String
evidenceBlockedBody conditional =
  "evidence affecting this claim's argumentation graph was quarantined as internally inconsistent (§4.3), and the "
    ++ "removed material could have changed the outcome, so no status is reported. On the "
    ++ "remaining evidence alone the claim would be "
    ++ statusWord conditional
    ++ ", but that label is conditional on evidence the checker refused to admit."

-- | The heading word for a public status: the canonical wire tag for a
-- quarantine-affected claim, the four-state word otherwise (issue #76).
publicStatusWord :: PublicStatus -> String
publicStatusWord ps = case ps of
  EvidenceBlocked _ -> tagToString TEvidenceBlocked
  Published s -> statusWord s

-- | The status word as it appears in a review heading\/summary for an ordinary
-- four-state status.
statusWord :: Status -> String
statusWord s = case s of
  Gap -> "gap"
  Justified -> "justified"
  Contested -> "contested"
  Defeated -> "defeated"

-- | Whether a declared conclusion supports a declared claim.
isSupportsClaim :: ArgConcl -> Bool
isSupportsClaim (SupportsClaim _) = True
isSupportsClaim _ = False

-- | The surface attack keyword.
attackKind :: Attack -> String
attackKind a = case a of
  Rebut {} -> "rebut"
  Undercut {} -> "undercut"
  Undermine {} -> "undermine"

-- | @(source id, target id)@ of a typed attack.
attackEndpoints :: Attack -> (String, String)
attackEndpoints a = case a of
  Rebut (ArgId s) (ArgId t) -> (s, t)
  Undercut (ArgId s) (ArgId t) _ -> (s, t)
  Undermine (ArgId s) (ArgId t) _ -> (s, t)

-- | Count occurrences by /rendered/ status word, most-frequent first (ties by
-- spelling) — the same determinism discipline "Lara.ClaimSupport".@tally@ uses.
-- The key is the rendered word, not the 'PublicStatus' value:
-- 'publicStatusWord' erases the conditional label of every @EvidenceBlocked _@,
-- so tallying by value would split one public @evidence-blocked@ category by a
-- label the summary never shows.
statusTally :: [PublicStatus] -> [(String, Int)]
statusTally xs =
  sortBy (comparing (negate . snd) <> comparing fst)
    [(w, length (filter (== w) words')) | w <- distinct words']
  where
    words' = map publicStatusWord xs
    distinct = foldr (\x acc -> if x `elem` acc then acc else x : acc) []

-- | Render an argument\/id token in backticks.
tick :: String -> String
tick s = "`" ++ s ++ "`"

-- | Join with @\", \"@ (a short deterministic list).
commaList :: [String] -> String
commaList = intercalate ", "

-- | Upper-case the first character of a sentence (headings read the review as
-- prose; the templates start lower-case for reuse mid-sentence).
upcaseFirst :: String -> String
upcaseFirst [] = []
upcaseFirst (c : cs) = toUpperAscii c : cs
  where
    toUpperAscii x
      | x >= 'a' && x <= 'z' = toEnum (fromEnum x - 32)
      | otherwise = x
