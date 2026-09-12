-- | Conformance tests for the possible-world outer runtime (#322): the
-- @pw-run 1@ / @pw-surface 1@ codecs ("Lara.PW.Wire"), posing, translation and
-- comparison ("Lara.PW.Sorted"), and the run pipeline ("Lara.PW.Run").
--
-- These are conformance evidence, not soundness: the Lean development proves
-- the definitions these functions transcribe (@Run.decodeRun_encode@,
-- @Sorted.vocabFault_eq_none_iff@, @Model.evaluates_iff@, …), and
-- @scripts\/check-pw-conformance.py@ compares the two runtimes byte for byte.
-- Here the Haskell side is held to the same statements in-process:
--
--   * __committed goldens__ — every @fixtures\/pw\/run\/*.sexp@ and
--     @fixtures\/pw\/source\/*.sexp@ runs to its @*.expected@ bytes without
--     the CLI, and the document 'deriveRunFile' derives from it — every
--     source inline — runs to the same bytes (#327);
--   * __groups__ — a duplicate-report group whose members agree changes no
--     answer, and a conflicting group is refused by name, under both
--     conflict modes (#326);
--   * __round trips__ — structured and textual, over generated documents
--     whose names include quotes, backslashes, newlines, Unicode and the
--     empty string;
--   * __the malformed matrix__ — each decoder names the construct Lean's
--     names, so the error envelopes the gate compares cannot drift;
--   * __the mirrored laws__ — posing splits exactly the two Σ faults, the
--     vocabulary scan is exactly the translation's domain, symbol maps are
--     first-match, a posing fault consults no world, a comparison profile
--     is the accepted candidates' statuses in edge order, the rule clause
--     holds exactly when the target carries the rule's translation, and every
--     result keyword has its own spelling.
module PWSpec (pwSpecProps) where

import Data.List (isPrefixOf, isSuffixOf, nub, sort)
import Data.Maybe (isJust, isNothing)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import System.Directory (listDirectory)
import System.FilePath (replaceExtension, (</>))
import Test.QuickCheck

import Lara.AST
  ( AtomPat (..)
  , GroupId (..)
  , LeafId (..)
  , Mode (..)
  , Necessity (..)
  , Param (..)
  , Pat (..)
  , Question (..)
  , QuestionId (..)
  , Rule (..)
  , RuleId (..)
  , Status (..)
  )
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.PW.Run
import Lara.PW.Sorted
import Lara.PW.Surface
import Lara.PW.Wire
import Lara.Sigma (sigmaOf)
import Lara.Strict (SExpr (..))
import Lara.Wire (printSExpr)

-- ---------------------------------------------------------------------------
-- Generators
-- ---------------------------------------------------------------------------

-- | Identifier and payload text, including every character the printer must
-- quote or escape.
genName :: Gen String
genName =
  elements ["a", "b", "src", "tgt", "β bridge", "q\"uote", "back\\slash", "new\nline", "", "x y", "世界"]

genTerm :: Int -> Gen Term
genTerm n =
  oneof $
    [ TNum <$> elements ["1", "01.00", "-2", "+3.5"]
    , TStr <$> genName
    ]
      ++ [TCon . FunSym <$> genName <*> resize 2 (listOf (genTerm (n `div` 2))) | n > 0]

genProp :: Gen Prop
genProp = Prop . Pred <$> genName <*> resize 2 (listOf (genTerm 2))

genStatus :: Gen Status
genStatus = elements [Gap, Justified, Contested, Defeated]

genForm :: Int -> Gen SForm
genForm n
  | n <= 0 = oneof [SStatus <$> genStatus <*> genProp, pure STop]
  | otherwise =
      oneof
        [ SStatus <$> genStatus <*> genProp
        , pure STop
        , SNeg <$> genForm (n - 1)
        , SConj <$> genForm (n `div` 2) <*> genForm (n `div` 2)
        , SBox . BridgeId <$> genName <*> genForm (n - 1)
        , SDia . BridgeId <$> genName <*> genForm (n - 1)
        ]

genBridgeDecl :: Gen BridgeDecl
genBridgeDecl =
  BridgeDecl
    <$> (BridgeId <$> genName)
    <*> (CtxId <$> genName)
    <*> (CtxId <$> genName)
    <*> resize 3 (listOf (oneof [SymPred <$> (Pred <$> genName) <*> (Pred <$> genName), SymCon <$> (FunSym <$> genName) <*> (FunSym <$> genName)]))
    <*> resize 2 (listOf (LeafEntry <$> (LeafId <$> genName) <*> (LeafId <$> genName)))
    <*> resize 4 (listOf (elements clauseAll))

genDocument :: Gen Document
genDocument =
  Document
    <$> resize 2 (listOf genBridgeDecl)
    <*> resize 3 (listOf (Posed . CtxId <$> genName <*> genForm 4))

genSExpr :: Int -> Gen SExpr
genSExpr n
  | n <= 0 = SAtom <$> genName
  | otherwise = oneof [SAtom <$> genName, SList <$> resize 3 (listOf (genSExpr (n `div` 2)))]

genRunDoc :: Gen RunDoc
genRunDoc =
  RunDoc
    <$> resize 3 (listOf (WorldDecl <$> (WorldId <$> genName) <*> (CtxId <$> genName) <*> oneof [SourceInline <$> genSExpr 3, SourceFile <$> genName, SourceLara <$> genName]))
    <*> resize 3 (listOf (EdgeDecl <$> (BridgeId <$> genName) <*> (WorldId <$> genName) <*> (WorldId <$> genName) <*> elements [Accepted, Rejected]))
    <*> resize 3 (listOf (CompareDecl <$> (BridgeId <$> genName) <*> (WorldId <$> genName) <*> genProp))
    <*> genDocument

-- ---------------------------------------------------------------------------
-- Committed goldens
-- ---------------------------------------------------------------------------

-- | The committed run documents: envelope worlds, and @.lara@ worlds.
fixtureDirs :: [FilePath]
fixtureDirs = ["fixtures/pw/run", "fixtures/pw/source"]

fixturePaths :: IO [FilePath]
fixturePaths =
  concat
    <$> mapM
      (\dir -> map (dir </>) . sort . filter (".sexp" `isSuffixOf`) <$> listDirectory dir)
      fixtureDirs

renderResult :: Either PWError Outcome -> String
renderResult = either (printSExpr . encodeError) (printSExpr . encodeOutcome)

-- | Every committed run document produces its golden bytes in-process.
prop_goldenFixtures :: Property
prop_goldenFixtures = once $ ioProperty $ do
  files <- fixturePaths
  results <- mapM check files
  pure (conjoin (counterexample "no fixtures" (length files > 1) : results))
  where
    check path = do
      expected <- readFile (replaceExtension path "expected")
      outcome <- runPWFile path
      pure $ counterexample path $ case outcome of
        Left err -> counterexample (printSExpr (encodeError err)) False
        Right o -> printSExpr (encodeOutcome o) ++ "\n" === expected

-- | The inputs of a document whose sources are all inline; 'Nothing' if one
-- is not.
inlineInputs :: RunDoc -> Maybe [WorldInput]
inlineInputs doc = mapM input (rdWorlds doc)
  where
    input d = case wdSource d of
      SourceInline e -> Just (WorldInput (wdId d) (wdContext d) (Right e))
      _ -> Nothing

-- | Derivation preserves every fixture's run (#327): the derived document
-- has only inline sources, and running it gives the fixture's golden — the
-- in-process half of what the gate checks across both drivers.
prop_derivationPreservesRuns :: Property
prop_derivationPreservesRuns = once $ ioProperty $ do
  files <- fixturePaths
  results <- mapM check files
  pure (conjoin results)
  where
    check path = do
      expected <- readFile (replaceExtension path "expected")
      derived <- deriveRunFile path
      pure $ counterexample path $ case derived of
        Left err -> counterexample (printSExpr (encodeError err)) False
        Right doc -> case inlineInputs doc of
          Nothing -> counterexample "a source was not inlined" False
          Just inputs -> renderResult (runPW doc inputs) ++ "\n" === expected

-- | Run a document given as text with inline worlds only.
runInlineText :: String -> Either PWError Outcome
runInlineText text = do
  doc <- either (Left . PWWire) Right (decodeText text)
  inputs <- maybe (Left (PWIO "a source was not inline")) Right (inlineInputs doc)
  runPW doc inputs

-- | Replace @old@ by @new@, or fail loudly, so a stale fixture cannot turn a
-- case into a rerun of the unmodified input.
substitute :: String -> String -> String -> Either String String
substitute old new text = case breakOn old text of
  Nothing -> Left ("substitution target absent: " ++ old)
  Just (before, after) -> Right (before ++ new ++ after)
  where
    breakOn needle hay = go "" hay
      where
        go _ [] = Nothing
        go acc rest@(c : cs)
          | needle `isPrefixOf` rest = Just (reverse acc, drop (length needle) rest)
          | otherwise = go (c : acc) cs

-- | Duplicate-report groups (#326): a group whose members agree is inert
-- under both conflict modes, and a conflicting group refuses the world by
-- name, whatever the mode, naming the first such group. Each variant edits
-- the inline fixture's first world; l1 and l3 report p, l2 reports q, and l3
-- is added to both worlds because a context's leaf table is its environment.
prop_groupsInertOrRefused :: Property
prop_groupsInertOrRefused = once $ ioProperty $ do
  text <- readFile "fixtures/pw/run/inline.sexp"
  expected <- readFile "fixtures/pw/run/inline.expected"
  let withL3 = substitute "(leaf l2 (atom q)))" "(leaf l2 (atom q)) (leaf l3 (atom p)))" text
        >>= substitute "(leaf l2 (atom q)))" "(leaf l2 (atom q)) (leaf l3 (atom p)))"
      groups g = substitute "(queries (atom p))" ("(queries (atom p)) (groups " ++ g ++ ")")
      refused g = printSExpr (encodeError (PWWorld (WorldGroups (WorldId "w0") (GroupId g))))
      completes = (=== expected) . (++ "\n")
      run caseName variant check = counterexample caseName $ case variant of
        Left why -> counterexample why False
        Right t -> check (renderResult (runInlineText t))
  pure $
    conjoin
      [ run "conflict" (groups "quarantine (group g1 (l1 l2))" text) (=== refused "g1")
      , run "conflict under reject" (groups "reject (group g1 (l1 l2))" text) (=== refused "g1")
      , run "consistent" (withL3 >>= groups "quarantine (group g1 (l1 l3))") completes
      , run "consistent under reject" (withL3 >>= groups "reject (group g1 (l1 l3))") completes
      , run "first conflicting group named" (withL3 >>= groups "quarantine (group g0 (l1 l3)) (group g1 (l1 l2)) (group g2 (l2 l3))") (=== refused "g1")
      ]

-- ---------------------------------------------------------------------------
-- Codecs
-- ---------------------------------------------------------------------------

prop_runRoundTrip :: Property
prop_runRoundTrip = forAll genRunDoc $ \d -> decodeRun (encodeRun d) === Right d

-- | Through the shared printer and reader, not only the token tree.
prop_runTextRoundTrip :: Property
prop_runTextRoundTrip =
  forAll genRunDoc $ \d -> parseRunBS (TE.encodeUtf8 (T.pack (printRun d))) === Right d

decodeText :: String -> Either CodecError RunDoc
decodeText = parseRunBS . TE.encodeUtf8 . T.pack

-- | A valid run whose embedded document is @surface@.
withSurface :: String -> String
withSurface surface = "(pw-run 1 (worlds) (edges) (comparisons) " ++ surface ++ ")"

-- | Each decoder names the construct Lean's decoder names.
prop_malformedMatrix :: Property
prop_malformedMatrix =
  conjoin
    [ counterexample input (decodeText input === Left (CodecError tag detail))
    | (input, tag, detail) <-
        [ ("(pw-run 1 (worlds) (edges) (comparisons))", CodecMalformed, "run")
        , ("(pw-run 2 anything at all)", CodecUnsupportedVersion, "2")
        , ("(pw-run 01 (worlds) (edges) (comparisons) (pw-surface 1 (bridges) (queries)))", CodecUnsupportedVersion, "01")
        , ("(pw-runs 1)", CodecMalformed, "run")
        , ("(pw-run 1 (edges) (worlds) (comparisons) (pw-surface 1 (bridges) (queries)))", CodecMalformed, "worlds")
        , ("(pw-run 1 (worlds (world w c)) (edges) (comparisons) (pw-surface 1 (bridges) (queries)))", CodecMalformed, "world")
        , ("(pw-run 1 (worlds (world w c (file))) (edges) (comparisons) (pw-surface 1 (bridges) (queries)))", CodecMalformed, "world-source")
        , ("(pw-run 1 (worlds (world w c (lara))) (edges) (comparisons) (pw-surface 1 (bridges) (queries)))", CodecMalformed, "world-source")
        , ("(pw-run 1 (worlds (world w c (lara (p)))) (edges) (comparisons) (pw-surface 1 (bridges) (queries)))", CodecMalformed, "world-source")
        , ("(pw-run 1 (worlds) (edges (edge b w v yes)) (comparisons) (pw-surface 1 (bridges) (queries)))", CodecMalformed, "acceptance")
        , ("(pw-run 1 (worlds) (edges (edge b w yes)) (comparisons) (pw-surface 1 (bridges) (queries)))", CodecMalformed, "edge")
        , ("(pw-run 1 (worlds) (edges) (comparisons (compare b w)) (pw-surface 1 (bridges) (queries)))", CodecMalformed, "comparison")
        , ("(pw-run 1 (worlds) (edges) (comparisons (compare b w (atom))) (pw-surface 1 (bridges) (queries)))", CodecMalformed, "atom")
        , ("(pw-run 1 (worlds) (edges) (comparisons (compare b w (atom p (num)))) (pw-surface 1 (bridges) (queries)))", CodecMalformed, "term")
        , (withSurface "(pw-surface 1 (bridges))", CodecMalformed, "document")
        , (withSurface "(pw-surface 2 (bridges) (queries) (worlds))", CodecUnsupportedVersion, "2")
        , (withSurface "(pw-surface 1 (queries) (bridges))", CodecMalformed, "bridges")
        , (withSurface "(pw-surface 1 (bridges (bridge b c d (symbols (pred p)) (leaves) (clauses))) (queries))", CodecMalformed, "symbol-entry")
        , (withSurface "(pw-surface 1 (bridges (bridge b c d (symbols) (leaves (leaf l)) (clauses))) (queries))", CodecMalformed, "leaf-entry")
        , (withSurface "(pw-surface 1 (bridges (bridge b c d (symbols) (leaves) (clauses leaf-ok maybe))) (queries))", CodecMalformed, "clause")
        , (withSurface "(pw-surface 1 (bridges (bridge b c d (symbols) (clauses) (leaves))) (queries))", CodecMalformed, "leaves")
        , (withSurface "(pw-surface 1 (bridges (bridge b c (symbols) (leaves) (clauses))) (queries))", CodecMalformed, "bridge")
        , (withSurface "(pw-surface 1 (bridges) (queries (pose c)))", CodecMalformed, "posed-query")
        , (withSurface "(pw-surface 1 (bridges) (queries (pose c (maybe))))", CodecMalformed, "formula")
        , (withSurface "(pw-surface 1 (bridges) (queries (pose c (status maybe (atom p)))))", CodecMalformed, "status")
        ]
    ]
    .&&. counterexample "syntax" (fmap (const ()) (decodeText "(pw-run 1") `hasTag` CodecSyntax)
    .&&. counterexample "trailing form" (fmap (const ()) (decodeText (withSurface "(pw-surface 1 (bridges) (queries))" ++ " (x)")) `hasTag` CodecSyntax)
  where
    hasTag r tag = either codecErrorTag (const CodecMalformed) r === tag

-- ---------------------------------------------------------------------------
-- Mirrored laws
-- ---------------------------------------------------------------------------

-- | Posing separates exactly the two Σ-level faults (Lean
-- @queryFault_undeclaredPredicate_iff@ / @queryFault_illSortedArguments_iff@).
prop_queryFaultSplit :: Property
prop_queryFaultSplit =
  conjoin
    [ queryFault sg (atom "r" []) === Just (UndeclaredPredicate (Pred "r"))
    , queryFault sg (atom "p" [z]) === Just (IllSortedArguments (Pred "p"))
    , queryFault sg (atom "t" [TNum "1"]) === Just (IllSortedArguments (Pred "t"))
    , queryFault sg (atom "t" [TCon (FunSym "w") []]) === Just (IllSortedArguments (Pred "t"))
    , queryFault sg (atom "t" [z]) === Nothing
    , queryFault sg (atom "p" []) === Nothing
    ]
  where
    sg = sigmaOf ["Item"] [("z", [], "Item")] [("p", []), ("t", ["Item"])]
    atom p = Prop (Pred p)
    z = TCon (FunSym "z") []

genEntries :: Gen [SymEntry]
genEntries =
  resize 4 $
    listOf $
      oneof
        [ SymPred <$> (Pred <$> elements ["p", "q"]) <*> (Pred <$> elements ["p", "q", "r"])
        , SymCon <$> (FunSym <$> elements ["z", "w"]) <*> (FunSym <$> elements ["z", "w"])
        ]

genSmallProp :: Gen Prop
genSmallProp = Prop . Pred <$> elements ["p", "q", "r"] <*> resize 2 (listOf smallTerm)
  where
    smallTerm = oneof [TNum <$> elements ["1"], TCon . FunSym <$> elements ["z", "w"] <*> resize 1 (listOf (pure (TNum "2")))]

-- | The vocabulary scan is exactly the translation's domain (Lean
-- @vocabFault_eq_none_iff@).
prop_vocabFaultIsDomain :: Property
prop_vocabFaultIsDomain =
  forAll genEntries $ \entries -> forAll genSmallProp $ \a ->
    let m = symMapOf entries
     in isNothing (vocabFault m a) === isJust (trAtom m a)

-- | Declaration order decides: the first entry for a symbol wins.
prop_symMapFirstMatch :: Property
prop_symMapFirstMatch =
  predMap m (Pred "p") === Just (Pred "q")
    .&&. conMap m (FunSym "z") === Just (FunSym "w")
    .&&. predMap m (Pred "z") === Nothing
  where
    m = symMapOf [SymPred (Pred "p") (Pred "q"), SymCon (FunSym "z") (FunSym "w"), SymPred (Pred "p") (Pred "r")]

-- | A comparison profile lists the accepted candidates' statuses in
-- candidate order, and the two reasons that survive posing are pinned to
-- their conditions (Lean @compare_no_candidate@ / @compare_all_rejected@ /
-- @mem_compare_profile_iff@).
prop_crossCompareLaws :: Property
prop_crossCompareLaws =
  forAll (resize 5 (listOf ((,) <$> arbitrary <*> genStatus))) $ \cands ->
    let result = crossCompare (Just ()) cands fst (\c () -> snd c)
     in case [s | (True, s) <- cands] of
          _ | null cands -> result === Incomparable NoCandidateWorld
          [] -> result === Incomparable AllCandidateBridgesRejected
          s : ss -> result === Comparable s ss

-- | A posing fault is decided before any world is consulted (Lean
-- @notPosable_world_independent@).
prop_posingWorldIndependent :: Property
prop_posingWorldIndependent =
  forAll genEntries $ \entries -> forAll genSmallProp $ \a ->
    forAll (resize 4 (listOf ((,) <$> arbitrary <*> genStatus))) $ \cands ->
      let m = symMapOf entries
          withCands cs = crossComparePosed sgS sgT m a cs fst (\c _ -> snd c)
       in case withCands [] of
            NotPosable f -> withCands cands === NotPosable f
            Compared _ -> property True
  where
    sgS = sigmaOf ["Item"] [("z", [], "Item")] [("p", []), ("q", ["Item"])]
    sgT = sigmaOf [] [] [("p", []), ("r", [])]

-- | The clause spellings, in scan order, are Lean's @Clause.all@. This
-- property only compares the Haskell table with a literal. That the two
-- runtimes scan in this order is pinned by the gate's two @within bridge:
-- clause scan order@ cases: keeping only @cert-ok@ reports @leaf-ok@, and
-- keeping only @leaf-ok@ reports @rule-ok@.
prop_clauseOrder :: Property
prop_clauseOrder = map clauseText clauseAll === ["leaf-ok", "rule-ok", "cert-ok"]

genSmallPat :: Gen Pat
genSmallPat =
  oneof
    [ PVar . Param <$> elements ["X", "Y"]
    , pure (PLit (TNum "1"))
    , PCon . FunSym <$> elements ["z", "w"] <*> resize 1 (listOf (PVar . Param <$> elements ["X", "Y"]))
    ]

genSmallAtomPat :: Gen AtomPat
genSmallAtomPat = AtomPat . Pred <$> elements ["p", "q", "r"] <*> resize 2 (listOf genSmallPat)

-- | A rule over 'genEntries'' vocabulary, so symbol maps hit and miss its
-- premises, conclusion, constructor sub-patterns and question answers.
genSmallRule :: Gen Rule
genSmallRule = do
  rid <- elements ["r1", "r2"]
  premises <- resize 2 (listOf genSmallAtomPat)
  conclusion <- genSmallAtomPat
  questions <-
    resize 2 (listOf (Question . QuestionId <$> elements ["cq1", "cq2"] <*> genSmallAtomPat <*> elements [Mandatory, Optional]))
  pure
    Rule
      { ruleId = RuleId rid
      , ruleParams = [Param "X", Param "Y"]
      , ruleMode = Defeasible
      , rulePremises = premises
      , rulePremiseLabels = []
      , ruleConclusion = conclusion
      , ruleAllowTrusted = False
      , ruleCertifiers = []
      , ruleQuestions = questions
      }

-- | For one source rule, the rule clause holds exactly when the target's
-- rule is the source rule's translation (Lean @ruleOkB_iff@). The candidate
-- targets are the translation itself, the untranslated rule, and an
-- unrelated rule.
prop_ruleOkIsTranslation :: Property
prop_ruleOkIsTranslation =
  forAll genEntries $ \entries -> forAll genSmallRule $ \r -> forAll genSmallRule $ \other ->
    let m = symMapOf entries
        targets = maybe id (:) (trRule m r) [r, other]
     in conjoin [counterexample (show t) (ruleOk m [r] [t] === (trRule m r == Just t)) | t <- targets]

-- | Every result-protocol keyword has its own spelling, so no two
-- constructors print alike (Lean @ResultTag.text_injective@).
prop_resultTagTableInjective :: Property
prop_resultTagTableInjective =
  let texts = map resultTagText [minBound .. maxBound :: ResultTag]
   in length (nub texts) === length texts

-- | Undecodable or unreadable run files exit 2; refused runs exit 1.
prop_exitCodes :: Property
prop_exitCodes =
  pwErrorExitCode (PWWire (CodecError CodecSyntax "")) === 2
    .&&. pwErrorExitCode (PWIO "") === 2
    .&&. pwErrorExitCode (PWWorld (DuplicateWorld (WorldId "w"))) === 1
    .&&. pwErrorExitCode (PWQuery (UnknownContext (CtxId "c"))) === 1

pwSpecProps :: [(String, IO Result)]
pwSpecProps =
  [ ("pw committed run goldens", quickCheckResult prop_goldenFixtures)
  , ("pw derivation preserves every fixture's run", quickCheckResult prop_derivationPreservesRuns)
  , ("pw consistent groups are inert, conflicting groups refused", quickCheckResult prop_groupsInertOrRefused)
  , ("pw-run structured round trip", quickCheckResult prop_runRoundTrip)
  , ("pw-run text round trip", quickCheckResult prop_runTextRoundTrip)
  , ("pw malformed matrix names Lean's constructs", quickCheckResult prop_malformedMatrix)
  , ("pw posing splits the two sigma faults", quickCheckResult prop_queryFaultSplit)
  , ("pw vocabulary scan is the translation domain", quickCheckResult prop_vocabFaultIsDomain)
  , ("pw symbol maps are first-match", quickCheckResult prop_symMapFirstMatch)
  , ("pw comparison profile and reasons", quickCheckResult prop_crossCompareLaws)
  , ("pw posing faults consult no world", quickCheckResult prop_posingWorldIndependent)
  , ("pw clause scan order", quickCheckResult prop_clauseOrder)
  , ("pw rule clause is the rule's translation", quickCheckResult prop_ruleOkIsTranslation)
  , ("pw result keywords spelled once", quickCheckResult prop_resultTagTableInjective)
  , ("pw error exit codes", quickCheckResult prop_exitCodes)
  ]
