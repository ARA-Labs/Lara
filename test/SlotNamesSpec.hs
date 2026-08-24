-- | Premise-slot attribution on a backend rejection (#130,
-- "Lara.Elaborate.SlotNames").
--
-- The contract under test is one stderr block: when a registered backend
-- refuses a certificate, the reason names a @(prem i)@ and these lines say what
-- @i@ is. Two readings exist and both are pinned here —
--
--   * the __structural__ one ('Lara.Driver.slotMappingLines'), read off the
--     checked 'Lara.AST.Unit', which is all a raw @.sexp@ input can offer; and
--   * the __authored__ one ('Lara.Elaborate.renderAuthoredSlots'), which
--     recovers the leaf, prior-argument, and premise-label names the source
--     wrote, and is what the @.lara@ door prints.
--
-- The interesting cases are the ones where the two /differ/: a premise filled
-- by a prior argument (structural says @derived by \<rule\>@, authored says
-- @arg a1@), and a rule that labels its slots (only the authored reading has
-- labels at all, since labels never enter 'Lara.AST.Unit'). "CliSpec" pins the
-- binary's bytes for the leaf-only case where the two coincide.
module SlotNamesSpec (slotNamesSpecProps) where

import Test.QuickCheck

import Lara.AST
  ( ArgId (..)
  , LeafId (..)
  , Policy
  , PremiseLabel (..)
  , Program
  , RuleId (..)
  )
import Lara.Driver (slotMappingLines)
import Lara.Elaborate
  ( PreparedSource (..)
  , prepareSource
  , renderSourceInvalid
  , runSourceCheck
  , sourceResultAuthorDiagnostics
  , sourceResultAuthoredSlots
  , sourceResultSlotSources
  , slotMappingFor
  )
import Lara.Elaborate.SlotNames
  ( AuthoredReferent (..)
  , AuthoredSlot (..)
  , renderAuthoredSlots
  )
import Lara.Admission (renderAdmissionRejection)
import Lara.SupportTerm (SlotSource (..))
import Lara.Syntax (parsePolicy, parseProgram)

-- ---------------------------------------------------------------------------
-- Fixtures
-- ---------------------------------------------------------------------------

-- | The two equal cells of @examples\/S3@ under a policy whose recheck rule
-- concludes @num_lt@: the certificate replays false, so every fixture below
-- rejects at a checker-side R13 and reaches the slot rendering.
--
-- @labels@ selects whether the strict rule declares premise labels; the rest of
-- the artifact is identical, so a difference in output is a difference the
-- labels made.
tiePolicy :: Bool -> String
tiePolicy labels =
  tiePolicyLabelled
    (if labels then [Just "base", Just "candidate"] else [Nothing, Nothing])

-- | 'tiePolicy' with each premise's label chosen independently, so a block can
-- label some slots and not others — legal per grammar App. B.4, and the case
-- where padding must not run past a label that is not there.
tiePolicyLabelled :: [Maybe String] -> String
tiePolicyLabelled labels =
  unlines
    [ "policy p"
    , "sort System, Measurand, Dataset, Experiment, Cell"
    , "con sys_new : System"
    , "con sys_base : System"
    , "con accuracy : Measurand"
    , "con imagenet_val : Dataset"
    , "con exp1 : Experiment"
    , "con score_cell(System, Measurand, Dataset, Num) : Cell"
    , "pred reports(Experiment, Cell)"
    , "pred num_lt(Num, Num)"
    , "rule beats_recheck(S, B, Q, D, Exp, Sv, Bv)"
    , "  mode       = strict"
    , "  premises   = [ " ++ label 0 ++ "reports(Exp, score_cell(B, Q, D, Bv)),"
    , "                 " ++ label 1 ++ "reports(Exp, score_cell(S, Q, D, Sv)) ]"
    , "  conclusion = num_lt(Bv, Sv)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:t0) ]"
    , "theory sha256:t0 = []"
    ]
  where
    label i = case drop i labels of
      Just l : _ -> l ++ ": "
      _ -> ""

tieProgram :: String
tieProgram =
  unlines
    [ "artifact ord_tie_demo at sha256:5353535353535353535353535353535353535353535353535353535353535353"
    , "policy p"
    , "use backends [ord@1]"
    , "claim c2"
    , "  nl      = \"The baseline accuracy is below the system accuracy\""
    , "  formal  = num_lt(0.71, 0.71)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , "leaf e1 : reports(exp1, score_cell(sys_base, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_base]"
    , "leaf e2 : reports(exp1, score_cell(sys_new, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_new]"
    , "arg a1 : supports(c2) by beats_recheck(sys_new, sys_base, accuracy, imagenet_val, exp1, 0.71, 0.71)"
    , "  assurance = cert(ord@1, sha256:t0, (ordcmp (prem 0) (prem 1)))"
    , "status c2"
    ]

-- | A strict, certificate-bearing step whose first premise is a __prior
-- argument__ rather than a leaf — the one shape where the structural and
-- authored readings genuinely disagree.
--
-- Premise resolution inlines @a1@ as its own elaborated term, so 'Lara.AST.Unit'
-- retains the bridging rule and not the name @a1@; only the source door can put
-- the authored id back. @ord\@1@ refuses the resulting cite (its premises are
-- not both numeric cells), which is exactly the R13 this exercises.
nestedPolicy :: String
nestedPolicy =
  unlines
    [ "policy p"
    , "sort System, Measurand, Dataset, Experiment, Cell"
    , "con sys_new : System"
    , "con sys_base : System"
    , "con accuracy : Measurand"
    , "con imagenet_val : Dataset"
    , "con exp1 : Experiment"
    , "con score_cell(System, Measurand, Dataset, Num) : Cell"
    , "pred reports(Experiment, Cell)"
    , "pred derived_cell(System)"
    , "pred num_lt(Num, Num)"
    , "rule bridge(X)"
    , "  mode       = defeasible"
    , "  premises   = [ reports(exp1, score_cell(X, accuracy, imagenet_val, 0.71)) ]"
    , "  conclusion = derived_cell(X)"
    , "rule beats_recheck(S, B)"
    , "  mode       = strict"
    , "  premises   = [ prior: derived_cell(B),"
    , "                 cell: reports(exp1, score_cell(S, accuracy, imagenet_val, 0.71)) ]"
    , "  conclusion = num_lt(0.71, 0.71)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:t0) ]"
    , "theory sha256:t0 = []"
    ]

nestedProgram :: String
nestedProgram =
  unlines
    [ "artifact ord_nested_demo at sha256:5353535353535353535353535353535353535353535353535353535353535353"
    , "policy p"
    , "use backends [ord@1]"
    , "claim c2"
    , "  nl      = \"The baseline accuracy is below the system accuracy\""
    , "  formal  = num_lt(0.71, 0.71)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , "claim c1"
    , "  nl      = \"The baseline cell is a derived cell\""
    , "  formal  = derived_cell(sys_base)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , "leaf e1 : reports(exp1, score_cell(sys_base, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_base]"
    , "leaf e2 : reports(exp1, score_cell(sys_new, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_new]"
    , "arg a1 : supports(c1) by bridge(sys_base)"
    , "arg a2 : supports(c2) by beats_recheck(sys_new, sys_base)"
    , "  assurance = cert(ord@1, sha256:t0, (ordcmp (prem 0) (prem 1)))"
    , "status c2"
    ]

-- | 'nestedProgram' with the bridging argument declared __twice__, and the
-- rejected argument citing the second copy by name.
--
-- @a1@ and @a1b@ are separate declarations of the same rule under the same
-- substitution, so they elaborate to @Eq@-equal 'Lara.AST.SupportTerm's —
-- equality there is structural and carries no identity. The @from [...]@
-- citation resolves @a1b@ by /name/, so nothing upstream rejects the duplicate;
-- only the slot lookup sees two candidates, and its answer must be the
-- structural one rather than whichever copy happens to be declared first.
ambiguousProgram :: String
ambiguousProgram =
  unlines
    [ "artifact ord_ambiguous_demo at sha256:5353535353535353535353535353535353535353535353535353535353535353"
    , "policy p"
    , "use backends [ord@1]"
    , "claim c2"
    , "  nl      = \"The baseline accuracy is below the system accuracy\""
    , "  formal  = num_lt(0.71, 0.71)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , "claim c1"
    , "  nl      = \"The baseline cell is a derived cell\""
    , "  formal  = derived_cell(sys_base)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , "leaf e1 : reports(exp1, score_cell(sys_base, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_base]"
    , "leaf e2 : reports(exp1, score_cell(sys_new, accuracy, imagenet_val, 0.71))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/tables/accuracy.md#row=sys_new]"
    , "arg a1 : supports(c1) by bridge(sys_base)"
    , "arg a1b : supports(c1) by bridge(sys_base)"
    , "arg a2 : supports(c2) by beats_recheck from [a1b, e2]"
    , "  assurance = cert(ord@1, sha256:t0, (ordcmp (prem 0) (prem 1)))"
    , "status c2"
    ]

-- ---------------------------------------------------------------------------
-- Harness
-- ---------------------------------------------------------------------------

parsed :: String -> String -> Either String (Program, Policy)
parsed programSource policySource = do
  program <- either (Left . show) Right (parseProgram programSource)
  policy <- either (Left . show) Right (parsePolicy policySource)
  pure (program, policy)

-- | The author-facing stderr lines of one source artifact — what @lara check@
-- prints on the @.lara@ door.
authorLines :: String -> String -> Either String [String]
authorLines programSource policySource = do
  (program, policy) <- parsed programSource policySource
  case prepareSource program policy of
    Left invalid -> Left ("source invalid: " ++ renderSourceInvalid invalid)
    Right (SourceRejected rejection) ->
      Left ("admission rejection: " ++ renderAdmissionRejection rejection)
    Right (SourceAccepted input) ->
      Right (sourceResultAuthorDiagnostics (runSourceCheck input))

-- | The structural mapping the same artifact carries — what a raw @.sexp@ input
-- with these bytes would print.
structuralSlots :: String -> String -> Either String [SlotSource]
structuralSlots programSource policySource = do
  (program, policy) <- parsed programSource policySource
  case prepareSource program policy of
    Left invalid -> Left ("source invalid: " ++ renderSourceInvalid invalid)
    Right (SourceRejected rejection) ->
      Left ("admission rejection: " ++ renderAdmissionRejection rejection)
    Right (SourceAccepted input) ->
      Right (sourceResultSlotSources (runSourceCheck input))

authoredMap :: String -> String -> Either String [(ArgId, [AuthoredSlot])]
authoredMap programSource policySource = do
  (program, policy) <- parsed programSource policySource
  case prepareSource program policy of
    Left invalid -> Left ("source invalid: " ++ renderSourceInvalid invalid)
    Right (SourceRejected rejection) ->
      Left ("admission rejection: " ++ renderAdmissionRejection rejection)
    Right (SourceAccepted input) ->
      Right (sourceResultAuthoredSlots (runSourceCheck input))

-- | Every line after the backend's reason: the slot block alone.
slotBlock :: [String] -> [String]
slotBlock = drop 1 . dropWhile (not . isReason)
  where
    isReason l = take 20 l == "certificate replay: "

-- ---------------------------------------------------------------------------
-- The authored reading
-- ---------------------------------------------------------------------------

-- | Leaf-fed slots with no declared labels: the authored reading names the
-- leaves the source declares, one line per slot, with no label column.
prop_authoredLeafSlots :: Property
prop_authoredLeafSlots = once $
  case authorLines tieProgram (tiePolicy False) of
    Left err -> counterexample err False
    Right ls ->
      slotBlock ls
        === [ "  slot 0 = leaf e1"
            , "  slot 1 = leaf e2"
            ]

-- | The same artifact under a rule that labels its premises: each line gains
-- the label, and the referents are padded so the labels align.
--
-- This is the reading that has no structural counterpart at all —
-- 'Lara.AST.rulePremiseLabels' is stripped on the way into 'Lara.AST.Unit'
-- (grammar App. B.4), so the raw door cannot print a label even in principle.
prop_authoredSlotLabels :: Property
prop_authoredSlotLabels = once $
  case authorLines tieProgram (tiePolicy True) of
    Left err -> counterexample err False
    Right ls ->
      slotBlock ls
        === [ "  slot 0 = leaf e1  [label: base]"
            , "  slot 1 = leaf e2  [label: candidate]"
            ]

-- | A premise filled by a prior argument prints that argument's __authored
-- id__, not the rule that concluded it.
--
-- This is the case that makes the source door worth a separate reading: the id
-- @a1@ exists nowhere in the checked 'Lara.AST.Unit', because premise
-- resolution inlined the argument as its own elaborated term.
prop_authoredPriorArgumentSlot :: Property
prop_authoredPriorArgumentSlot = once $
  case authorLines nestedProgram nestedPolicy of
    Left err -> counterexample err False
    Right ls ->
      slotBlock ls
        === [ "  slot 0 = arg a1   [label: prior]"
            , "  slot 1 = leaf e2  [label: cell]"
            ]

-- | The structural reading of that same artifact keeps the rule, confirming the
-- two readings really do disagree here rather than the authored one being a
-- relabelling of identical data.
prop_structuralKeepsTheRule :: Property
prop_structuralKeepsTheRule = once $
  case structuralSlots nestedProgram nestedPolicy of
    Left err -> counterexample err False
    Right slots ->
      slots === [SlotDerived (RuleId "bridge"), SlotLeaf (LeafId "e2")]

-- | The authored map covers every checked argument, not only the rejected one:
-- it is a property of the source, so the bridging argument @a1@ carries its own
-- slot spelling too.
prop_authoredMapCoversEveryArgument :: Property
prop_authoredMapCoversEveryArgument = once $
  case authoredMap nestedProgram nestedPolicy of
    Left err -> counterexample err False
    Right entries ->
      conjoin
        [ counterexample "both arguments are keyed" $
            map fst entries === [ArgId "a1", ArgId "a2"]
        , counterexample "the bridge's own premise is its leaf" $
            fmap (map asReferent) (lookup (ArgId "a1") entries)
              === Just [ARLeaf (LeafId "e1")]
        , counterexample "the rejected argument cites the prior one" $
            fmap (map asReferent) (lookup (ArgId "a2") entries)
              === Just [ARArg (ArgId "a1"), ARLeaf (LeafId "e2")]
        ]

-- | The duplicate never reaches a slot block at all: the checker refuses the
-- unit outright, so no @(prem i)@ is ever explained against an ambiguous map.
--
-- This is what makes the ambiguity unreachable end-to-end, and pinning it is
-- what ties the two facts together: @firstDuplicate@ scans exactly the checked
-- argument list the authored map is keyed over, so a unit that survives to a
-- backend rejection has pairwise distinct argument terms by construction.
prop_duplicateArgumentsPrintNoSlotBlock :: Property
prop_duplicateArgumentsPrintNoSlotBlock = once $
  case authorLines ambiguousProgram nestedPolicy of
    Left err -> counterexample err False
    Right ls ->
      counterexample (show ls) $
        property (not (any ((== "  slot ") . take 7) ls))

-- | Even so, the lookup itself declines to guess: in the map built from that
-- rejected unit, the citing argument's first slot names neither copy.
--
-- The invariant above is the checker's, not this module's, and this is the
-- regression that notices if it is ever relaxed — the answer stays the
-- less specific but true structural spelling instead of becoming whichever
-- duplicate happens to be declared first.
prop_ambiguousSiblingIsNotNamed :: Property
prop_ambiguousSiblingIsNotNamed = once $
  case authoredMap ambiguousProgram nestedPolicy of
    Left err -> counterexample err False
    Right entries ->
      conjoin
        [ counterexample "all three arguments are keyed" $
            map fst entries === [ArgId "a1", ArgId "a1b", ArgId "a2"]
        , counterexample "the two copies really are structurally equal" $
            (lookup (ArgId "a1") entries == lookup (ArgId "a1b") entries) === True
        , counterexample "the ambiguous slot names neither copy" $
            fmap (map asReferent) (lookup (ArgId "a2") entries)
              === Just [ARDerived (RuleId "bridge"), ARLeaf (LeafId "e2")]
        ]

-- | A block that labels some slots and not others pads only the labelled lines:
-- an unlabelled line has nothing to align, so padding it would append trailing
-- whitespace to bytes this project pins exactly.
prop_mixedLabelsPadOnlyLabelledSlots :: Property
prop_mixedLabelsPadOnlyLabelledSlots = once $
  case authorLines tieProgram (tiePolicyLabelled [Nothing, Just "candidate"]) of
    Left err -> counterexample err False
    Right ls ->
      slotBlock ls
        === [ "  slot 0 = leaf e1"
            , "  slot 1 = leaf e2  [label: candidate]"
            ]

-- | The renderer itself, on the mixed case, leaves no line ending in a space.
prop_mixedLabelsLeaveNoTrailingSpace :: Property
prop_mixedLabelsLeaveNoTrailingSpace = once $
  renderAuthoredSlots
    [ AuthoredSlot (ARDerived (RuleId "a_much_longer_rule")) Nothing
    , AuthoredSlot (ARLeaf (LeafId "e2")) (Just (PremiseLabel "cell"))
    ]
    === [ "  slot 0 = " ++ longest
        , "  slot 1 = leaf e2" ++ padding ++ "  [label: cell]"
        ]
  where
    longest = "derived by a_much_longer_rule"
    padding = replicate (length longest - length "leaf e2") ' '

-- ---------------------------------------------------------------------------
-- The structural reading
-- ---------------------------------------------------------------------------

-- | The fallback arm of 'Lara.Elaborate.slotMappingFor': with no authored
-- reading recovered, or with the two readings disagreeing on slot count, the
-- structural lines print unchanged.
--
-- No artifact reaches the mismatch arm today — both lists are built from the
-- same premise list, so their lengths agree by construction — which is exactly
-- why it is pinned here directly. The documented promise is that a future
-- change breaking that assumption degrades to the kernel's vocabulary rather
-- than printing nothing or printing a mapping of the wrong length.
prop_slotMappingFallsBackToStructural :: Property
prop_slotMappingFallsBackToStructural = once $
  conjoin
    [ counterexample "no authored reading" $
        slotMappingFor structural Nothing === structuralLines
    , counterexample "authored reading is too short" $
        slotMappingFor structural (Just (take 1 authored)) === structuralLines
    , counterexample "authored reading is too long" $
        slotMappingFor structural (Just (authored ++ authored)) === structuralLines
    , counterexample "lengths agree, so the authored reading wins" $
        slotMappingFor structural (Just authored)
          === ["  slot 0 = arg a1", "  slot 1 = leaf e2"]
    , counterexample "no slots to explain, whatever was recovered" $
        conjoin
          [ slotMappingFor [] Nothing === []
          , slotMappingFor [] (Just authored) === []
          ]
    ]
  where
    structural = [SlotDerived (RuleId "bridge"), SlotLeaf (LeafId "e2")]
    structuralLines = slotMappingLines structural
    authored =
      [ AuthoredSlot (ARArg (ArgId "a1")) Nothing
      , AuthoredSlot (ARLeaf (LeafId "e2")) Nothing
      ]


-- | The structural renderer covers both arms, and numbers slots from zero so
-- the lines index the @(prem i)@ the certificate cites.
prop_structuralRendering :: Property
prop_structuralRendering = once $
  slotMappingLines [SlotLeaf (LeafId "e0"), SlotDerived (RuleId "bridge")]
    === [ "  slot 0 = leaf e0"
        , "  slot 1 = derived by bridge"
        ]

-- | Empty in, empty out: a rejection with no premise list adds no lines, which
-- is what keeps every non-R13 class byte-unchanged.
prop_structuralEmpty :: Property
prop_structuralEmpty = once $ slotMappingLines [] === []

-- | An unnamed referent renders without a label column, so a rule that labels
-- none of its premises prints exactly the structural spelling.
prop_authoredRenderingWithoutLabels :: Property
prop_authoredRenderingWithoutLabels = once $
  renderAuthoredSlots
    [ AuthoredSlot (ARLeaf (LeafId "e1")) Nothing
    , AuthoredSlot (ARDerived (RuleId "bridge")) Nothing
    ]
    === [ "  slot 0 = leaf e1"
        , "  slot 1 = derived by bridge"
        ]

-- ---------------------------------------------------------------------------
-- Silence where there is nothing to explain
-- ---------------------------------------------------------------------------

-- | An accepting artifact prints no slot lines: the block exists only under a
-- backend's reason, and an accept has none.
prop_acceptIsSilent :: Property
prop_acceptIsSilent = once $
  case authorLines acceptingProgram acceptingPolicy of
    Left err -> counterexample err False
    Right ls -> ls === []
  where
    -- The tie artifact with its claim weakened to match: same two equal cells,
    -- same certificate, now a true comparison.
    acceptingProgram = replace "num_lt(0.71, 0.71)" "num_le(0.71, 0.71)" tieProgram
    replace from to s = case breakOn from s of
      Nothing -> s
      Just (before, after) -> before ++ to ++ replace from to after
    breakOn needle s = go "" s
      where
        go _ [] = Nothing
        go acc rest@(c : cs)
          | take (length needle) rest == needle =
              Just (reverse acc, drop (length needle) rest)
          | otherwise = go (c : acc) cs
    -- The same policy with @num_le@ restored: the two equal cells now compare
    -- true and the certificate replays.
    acceptingPolicy =
      unlines
        [ "policy p"
        , "sort System, Measurand, Dataset, Experiment, Cell"
        , "con sys_new : System"
        , "con sys_base : System"
        , "con accuracy : Measurand"
        , "con imagenet_val : Dataset"
        , "con exp1 : Experiment"
        , "con score_cell(System, Measurand, Dataset, Num) : Cell"
        , "pred reports(Experiment, Cell)"
        , "pred num_lt(Num, Num)"
        , "pred num_le(Num, Num)"
        , "rule beats_recheck(S, B, Q, D, Exp, Sv, Bv)"
        , "  mode       = strict"
        , "  premises   = [ reports(Exp, score_cell(B, Q, D, Bv)),"
        , "                 reports(Exp, score_cell(S, Q, D, Sv)) ]"
        , "  conclusion = num_le(Bv, Sv)"
        , "  allow-trusted = false"
        , "  certifiers = [ (ord@1, sha256:t0) ]"
        , "theory sha256:t0 = []"
        ]

slotNamesSpecProps :: [(String, IO Result)]
slotNamesSpecProps =
  [ ("#130 authored slots name the declared leaves", quickCheckResult prop_authoredLeafSlots)
  , ("#130 authored slots carry aligned premise labels", quickCheckResult prop_authoredSlotLabels)
  , ("#130 a prior-argument premise prints its authored id", quickCheckResult prop_authoredPriorArgumentSlot)
  , ("#130 the structural reading keeps the concluding rule", quickCheckResult prop_structuralKeepsTheRule)
  , ("#130 the authored map covers every checked argument", quickCheckResult prop_authoredMapCoversEveryArgument)
  , ("#130 duplicate arguments print no slot block", quickCheckResult prop_duplicateArgumentsPrintNoSlotBlock)
  , ("#130 the ambiguous slot names neither duplicate", quickCheckResult prop_ambiguousSiblingIsNotNamed)
  , ("#130 mixed labels pad only the labelled slots", quickCheckResult prop_mixedLabelsPadOnlyLabelledSlots)
  , ("#130 mixed labels leave no trailing whitespace", quickCheckResult prop_mixedLabelsLeaveNoTrailingSpace)
  , ("#130 the slot mapping falls back to the structural reading", quickCheckResult prop_slotMappingFallsBackToStructural)
  , ("#130 structural rendering covers both arms", quickCheckResult prop_structuralRendering)
  , ("#130 an empty mapping renders nothing", quickCheckResult prop_structuralEmpty)
  , ("#130 unlabelled authored slots drop the label column", quickCheckResult prop_authoredRenderingWithoutLabels)
  , ("#130 an accepting artifact prints no slot block", quickCheckResult prop_acceptIsSilent)
  ]
