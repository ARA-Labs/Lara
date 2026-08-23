-- | Conformance vectors for named natural-deduction proof-term lowering.
-- The fixtures exercise only the presentation pass: its result is an opaque
-- strict payload, ready for the existing backend decoder to validate.
module NDNamedSpec (ndNamedSpecProps) where

import Data.List (isInfixOf, isPrefixOf)
import qualified Data.Set as Set
import Test.QuickCheck

import Lara.AST
  ( ArgId (..)
  , ArgRef (..)
  , Program
  , Policy
  , RuleId (..)
  , Unit (..)
  , RejectClass (R13)
  , Rejection (..)
  )
import qualified Lara.AST as AST
import Lara.Driver (runCheck)
import Lara.Elaborate
  ( PreparedSource (..)
  , prepareSource
  , runSourceCheck
  , sourceResultVerdict
  )
import Lara.Elaborate.CertSlots (SlotRefError (..))
import Lara.Elaborate.Internal (ElabError (..), elaborate, elabErrorMessage, registryOf)
import Lara.Elaborate.NDNamed
  ( NamedRefError (..)
  , NamedTag (NTThy)
  , firstNamedMarker
  , lowerNamedPayload
  , namedTagToString
  )
import Lara.Prop (Pred (..), Prop (..))
import Lara.Replay
  ( CoreVersion (LaraCoreV02)
  , mkCheckInput
  , mkReplayId
  )
import qualified Lara.Strict as Strict
import Lara.Strict (SExpr (..))
import qualified Lara.Strict.Cell as Cell
import qualified Lara.Strict.ND as ND
import Lara.Syntax (parsePolicy, parseProgram, printProgram)
import Lara.Wire
  ( Outcome (..)
  , Verdict (..)
  , decodeUnit
  , encodeVerdict
  , encodeUnit
  , parseSExpr
  , printSExpr
  )

-- | The fixed two-premise resolver used by all vectors unless a vector needs
-- a deliberately shadowed premise name.
rho :: String -> Either SlotRefError Int
rho "a" = Right 0
rho "b" = Right 1
rho _ = Left SlotNameUnresolved

atom :: String -> SExpr
atom = SAtom

node :: String -> [SExpr] -> SExpr
node k = SList . (atom k :)

hyp :: String -> SExpr
hyp n = node (ND.tagToString ND.THyp) [atom n]

prem :: String -> SExpr
prem n = node (Cell.tagToString Cell.TPrem) [atom n]

thy :: String -> SExpr
thy n = node (namedTagToString NTThy) [atom n]

lam :: SExpr -> SExpr -> SExpr
lam f e = node (ND.tagToString ND.TLam) [f, e]

namedLam :: String -> SExpr -> SExpr -> SExpr
namedLam x f e = node (ND.tagToString ND.TLam) [atom x, f, e]

app :: SExpr -> SExpr -> SExpr
app f x = node (ND.tagToString ND.TApp) [f, x]

-- | The approved lowering vectors. Keeping each label, input, and expected
-- result in one triple makes it impossible for parallel lists to truncate
-- silently. Each result pins both the payload shape and the specific
-- presentation-layer rejection where one is required.
vectors :: [(String, SExpr, Either (String, NamedRefError) SExpr)]
vectors =
  [ ( "kernel proof remains unchanged"
    , hyp "0"
    , Right (hyp "0")
    )
  , ( "numeric premise lowers at depth zero"
    , prem "1"
    , Right (hyp "1")
    )
  , ( "anonymous binder shifts premise"
    , lam (atom "<F>") (prem "b")
    , Right (lam (atom "<F>") (hyp "2"))
    )
  , ( "named binder resolves to innermost hypothesis"
    , app (namedLam "h" (atom "<F>") (hyp "h")) (prem "a")
    , Right (app (lam (atom "<F>") (hyp "0")) (hyp "0"))
    )
  , ( "outer named binder shifts under nested binder"
    , namedLam "h" (atom "<F>") (namedLam "k" (atom "<G>") (hyp "h"))
    , Right (lam (atom "<F>") (lam (atom "<G>") (hyp "1")))
    )
  , ( "theory index shifts beyond premises"
    , lam (atom "<F>") (thy "0")
    , Right (lam (atom "<F>") (hyp "3"))
    )
  , ( "noncanonical theory numeral"
    , thy "007"
    , Left ("007", NamedNonCanonicalIndex)
    )
  , ( "nonnumeric theory index"
    , thy "zz"
    , Left ("zz", NamedNonCanonicalIndex)
    )
  , ( "out of range numeric premise"
    , prem "2"
    , Left ("2", NamedPremOutOfRange 2 2)
    )
  , ( "unbound named hypothesis"
    , hyp "x"
    , Left ("x", NamedBinderUnbound)
    )
  , ( "duplicate named binder"
    , namedLam "h" (atom "<F>") (namedLam "h" (atom "<G>") (hyp "h"))
    , Left ("h", NamedBinderShadowed)
    )
  , ( "malformed named binder"
    , namedLam "0" (atom "<F>") (hyp "0")
    , Left ("0", NamedMalformedBinder)
    )
  , ( "structured named binder"
    , node (ND.tagToString ND.TLam) [SList [atom "foo"], atom "<F>", hyp "0"]
    , Left ("(foo)", NamedMalformedBinder)
    )
  , ( "standalone noncanonical kernel index stays opaque"
    , hyp "007"
    , Right (hyp "007")
    )
  , ( "noncanonical premise numeral"
    , prem "007"
    , Left ("007", NamedPremSlot SlotNonCanonicalNumeral)
    )
  , ( "marker in formula position is residual"
    , lam (prem "a") (prem "b")
    , Left ("a", NamedResidual)
    )
  , ( "residual formula marker precedes body failure"
    , lam (node "imp" [prem "p", atom "false"]) (hyp "0")
    , Left ("p", NamedResidual)
    )
  , ( "marker under unknown constructor is residual"
    , node "foo" [prem "a"]
    , Left ("a", NamedResidual)
    )
  , ( "junk without a marker remains unchanged"
    , node "foo" [atom "bar"]
    , Right (node "foo" [atom "bar"])
    )
  , ( "unresolved named premise"
    , prem "q"
    , Left ("q", NamedPremSlot SlotNameUnresolved)
    )
  , ( "kernel index is rejected in named mode"
    , namedLam "h" (atom "<F>") (hyp "0")
    , Left ("0", NamedKernelIndex)
    )
  , ( "numeric premise shifts under named binder"
    , namedLam "h" (atom "<F>") (prem "0")
    , Right (lam (atom "<F>") (hyp "1"))
    )
  , ( "unicode binder with punctuation suffix is an identifier"
    , namedLam "é!" (atom "<F>") (hyp "é!")
    , Right (lam (atom "<F>") (hyp "0"))
    )
  , ( "binder cannot shadow premise"
    , namedLam "a" (atom "<F>") (prem "b")
    , Left ("a", NamedBinderShadowsPremise)
    )
  , ( "noncanonical index is rejected in named mode"
    , namedLam "h" (atom "<F>") (hyp "007")
    , Left ("007", NamedNonCanonicalIndex)
    )
  ]

-- | Each fixed vector is registered separately, so the test runner reports
-- the precise lowering contract that changed if one ever regresses.
vectorProps :: [(String, Bool)]
vectorProps =
  [ (vectorLabel, lowerNamedPayload rho 2 input == expected)
  | (vectorLabel, input, expected) <- vectors
  ]

ndNamedSpecProps :: [(String, IO Result)]
ndNamedSpecProps =
  [("named ND: " ++ vectorLabel, quickCheckResult (property passed)) | (vectorLabel, passed) <- vectorProps]
    ++
      [ ("named ND: parse/elaborate lowers S1 premise spelling", quickCheckResult prop_s1NamedPremiseTwin)
      , ("named ND: parse/elaborate lowers program-level binder vector", quickCheckResult prop_s1NamedBinderTwin)
      , ("named ND: theory references match the kernel free-context layout", quickCheckResult prop_theoryReferenceMatchesKernelLayout)
      , ("named ND: kernel payloads are marker-free and byte-identical", quickCheckResult prop_kernelPayloadConservative)
      , ("named ND: lowering agrees with an independent de Bruijn oracle", quickCheckResult prop_namedTranslationAgreesWithOracle)
      , ("named ND: oracle rejects unbound and shadowed binders", quickCheckResult prop_illScopedTermsMatchOracle)
      , ("named ND: canonical kernel hypotheses are forbidden in named mode", quickCheckResult prop_kernelHypInjectedIntoNamedTermIsRejected)
      , ("named ND: premise-name binder collision is forbidden", quickCheckResult prop_premiseNameBinderIsRejected)
      , ("named ND: named errors are located and exact", quickCheckResult prop_namedErrorMessages)
      , ("named ND: named premise failures reuse certificate-slot errors", quickCheckResult prop_namedPremiseUsesCertSlotError)
      , ("named ND: R13 boundary and named residual behavior", quickCheckResult prop_r13Boundary)
      , ("named ND: printer preserves named certificate atoms", quickCheckResult prop_namedPrinterRoundTrip)
      ]

-- The named lowering pass must be entirely conservative for the existing
-- kernel language.  A regression such as recognizing a kernel tag as a named
-- marker, or rebuilding a payload on its no-marker path, makes this fail.
genKernelFormula :: Int -> Gen ND.Formula
genKernelFormula n
  | n <= 0 = elements [ND.FFalse, kernelAtomFormula "P", kernelAtomFormula "Q", kernelAtomFormula "r"]
  | otherwise =
      frequency
        [ (3, genKernelFormula 0)
        , (2, ND.FImp <$> genKernelFormula (n `div` 2) <*> genKernelFormula (n `div` 2))
        ]

-- AtomId is intentionally opaque.  The public strict decoder is therefore
-- the legitimate constructor path for these known-valid kernel formula atoms.
kernelAtomFormula :: String -> ND.Formula
kernelAtomFormula source =
  case ND.decodeFormula (node (ND.tagToString ND.TAtom) [atom source]) of
    Right formula -> formula
    Left err -> error ("test atom did not decode: " ++ err)

genKernelCert :: Gen ND.Cert
genKernelCert = sized go
  where
    go n
      | n <= 0 = ND.Hyp <$> choose (0, 8)
      | otherwise =
          frequency
            [ (3, ND.Hyp <$> choose (0, 8))
            , (2, ND.Lam <$> genKernelFormula (n `div` 2) <*> go (n - 1))
            , (2, ND.App <$> go (n `div` 2) <*> go (n `div` 2))
            , (2, ND.Abort <$> genKernelFormula (n `div` 2) <*> go (n - 1))
            ]

formulaToSExpr :: ND.Formula -> SExpr
formulaToSExpr (ND.FAtom atomId) = node (ND.tagToString ND.TAtom) [atom (ND.atomIdString atomId)]
formulaToSExpr ND.FFalse = atom (ND.tagToString ND.TFalse)
formulaToSExpr (ND.FImp antecedent consequent) =
  node (ND.tagToString ND.TImp) [formulaToSExpr antecedent, formulaToSExpr consequent]

-- This encoder intentionally shares only the closed ND tag table, not the
-- named lowering implementation.  It is the independently owned kernel
-- payload producer for the conservativity property.
certToSExpr :: ND.Cert -> SExpr
certToSExpr (ND.Hyp index) = node (ND.tagToString ND.THyp) [atom (show index)]
certToSExpr (ND.Lam formula body) = node (ND.tagToString ND.TLam) [formulaToSExpr formula, certToSExpr body]
certToSExpr (ND.App fun argument) = node (ND.tagToString ND.TApp) [certToSExpr fun, certToSExpr argument]
certToSExpr (ND.Abort formula body) = node (ND.tagToString ND.TAbort) [formulaToSExpr formula, certToSExpr body]

genResolverCase :: Gen (Int, [(String, Int)])
genResolverCase = do
  nPrem <- choose (0, 6)
  names <- sublistOf ["a", "b", "c", "prem", "é"]
  slots <- vectorOf (length names) (choose (0, 6))
  pure (nPrem, zip names slots)

resolverFrom :: [(String, Int)] -> String -> Either SlotRefError Int
resolverFrom entries name = maybe (Left SlotNameUnresolved) Right (lookup name entries)

prop_kernelPayloadConservative :: Property
prop_kernelPayloadConservative =
  forAllShrink genKernelCert shrinkKernelCert $ \certificate ->
    forAll genResolverCase $ \(nPrem, entries) ->
      let payload = certToSExpr certificate
       in conjoin
            [ counterexample "kernel payload selected named mode" (firstNamedMarker payload === Nothing)
            , counterexample "kernel payload changed on named lowering's no-marker path" $
                lowerNamedPayload (resolverFrom entries) nPrem payload === Right payload
            ]

shrinkKernelCert :: ND.Cert -> [ND.Cert]
shrinkKernelCert (ND.Hyp index) = ND.Hyp <$> shrink index
shrinkKernelCert (ND.Lam formula body) = body : [ND.Lam formula body' | body' <- shrinkKernelCert body]
shrinkKernelCert (ND.App fun argument) = [fun, argument] ++ [ND.App fun' argument | fun' <- shrinkKernelCert fun] ++ [ND.App fun argument' | argument' <- shrinkKernelCert argument]
shrinkKernelCert (ND.Abort formula body) = body : [ND.Abort formula body' | body' <- shrinkKernelCert body]

-- The following language is deliberately test-local.  Unlike the product
-- lowering pass it models terms semantically, then translates them to ND.Cert
-- with an independently maintained binding environment.  In particular,
-- 'referenceIndex' counts anonymous binders too.
data NamedPremRef
  = PremNumber Integer
  | PremName String
  deriving (Eq, Show)

data NamedTerm
  = NamedHyp String
  | NamedPrem NamedPremRef
  | NamedThy Integer
  | NamedLam (Maybe String) ND.Formula NamedTerm
  | NamedApp NamedTerm NamedTerm
  | NamedAbort ND.Formula NamedTerm
  deriving (Eq, Show)

namedResolver :: [(String, Int)]
namedResolver = [("a", 0), ("b", 1), ("source", 2)]

namedPremiseCount :: Int
namedPremiseCount = 3

renderNamedTerm :: NamedTerm -> SExpr
renderNamedTerm (NamedHyp name) = hyp name
renderNamedTerm (NamedPrem (PremNumber slot)) = prem (show slot)
renderNamedTerm (NamedPrem (PremName name)) = prem name
renderNamedTerm (NamedThy slot) = thy (show slot)
renderNamedTerm (NamedLam Nothing formula body) = lam (formulaToSExpr formula) (renderNamedTerm body)
renderNamedTerm (NamedLam (Just name) formula body) = namedLam name (formulaToSExpr formula) (renderNamedTerm body)
renderNamedTerm (NamedApp fun argument) = app (renderNamedTerm fun) (renderNamedTerm argument)
renderNamedTerm (NamedAbort formula body) = node (ND.tagToString ND.TAbort) [formulaToSExpr formula, renderNamedTerm body]

referenceIndex :: String -> [Maybe String] -> Maybe Integer
referenceIndex wanted = go 0
  where
    go _ [] = Nothing
    go index (Nothing : rest) = go (index + 1) rest
    go index (Just name : rest)
      | wanted == name = Just index
      | otherwise = go (index + 1) rest

referenceLower :: [Maybe String] -> NamedTerm -> Either (String, NamedRefError) ND.Cert
referenceLower binders = go binders
  where
    go scope (NamedHyp name) =
      case referenceIndex name scope of
        Just index -> Right (ND.Hyp index)
        Nothing -> Left (name, NamedBinderUnbound)
    go scope (NamedPrem (PremNumber slot))
      | slot < toInteger namedPremiseCount = Right (ND.Hyp (toInteger (length scope) + slot))
      | otherwise = Left (show slot, NamedPremOutOfRange slot namedPremiseCount)
    go scope (NamedPrem (PremName name)) =
      case lookup name namedResolver of
        Just slot -> Right (ND.Hyp (toInteger (length scope) + toInteger slot))
        Nothing -> Left (name, NamedPremSlot SlotNameUnresolved)
    go scope (NamedThy slot) = Right (ND.Hyp (toInteger (length scope + namedPremiseCount) + slot))
    go scope (NamedLam binder formula body) = do
      case binder of
        Just name
          | Just _ <- referenceIndex name scope -> Left (name, NamedBinderShadowed)
          | Just _ <- lookup name namedResolver -> Left (name, NamedBinderShadowsPremise)
        _ -> Right ()
      ND.Lam formula <$> go (binder : scope) body
    go scope (NamedApp fun argument) = ND.App <$> go scope fun <*> go scope argument
    go scope (NamedAbort formula body) = ND.Abort formula <$> go scope body

-- The formula generator is shared with the kernel generator, while the term
-- generator chooses only references that its supplied scope can resolve.
-- Thus it does not discard malformed samples to obtain well-scoped terms.
genWellScopedNamedTerm :: Gen NamedTerm
genWellScopedNamedTerm = sized (go [])
  where
    go scope n
      | n <= 0 = genLeaf scope
      | otherwise =
          frequency
            [ (4, genLeaf scope)
            , (2, NamedLam Nothing <$> genKernelFormula (n `div` 3) <*> go (Nothing : scope) (n - 1))
            , (3, namedBinder scope n)
            , (2, NamedApp <$> go scope (n `div` 2) <*> go scope (n `div` 2))
            , (2, NamedAbort <$> genKernelFormula (n `div` 3) <*> go scope (n - 1))
            ]

    genLeaf scope =
      let binderNames = [name | Just name <- scope]
          freeLeaves =
            [ (3, NamedPrem . PremNumber <$> choose (0, toInteger (namedPremiseCount - 1)))
            , (3, NamedPrem . PremName <$> elements (map fst namedResolver))
            , (2, NamedThy <$> choose (0, 4))
            ]
          localLeaves = [(4, NamedHyp <$> elements binderNames) | not (null binderNames)]
       in frequency (freeLeaves ++ localLeaves)

    namedBinder scope n = do
      let name = "v" ++ show (length scope)
      NamedLam (Just name) <$> genKernelFormula (n `div` 3) <*> go (Just name : scope) (n - 1)

prop_namedTranslationAgreesWithOracle :: Property
prop_namedTranslationAgreesWithOracle =
  forAll genWellScopedNamedTerm $ \term ->
    let payload = renderNamedTerm term
     in case referenceLower [] term of
          Right certificate ->
            counterexample ("term: " ++ show term) $
              conjoin
                [ counterexample "well-scoped named term did not select named mode" (property (firstNamedMarker payload /= Nothing))
                , lowerNamedPayload (resolverFrom namedResolver) namedPremiseCount payload === Right (certToSExpr certificate)
                ]
          Left failure -> counterexample ("well-scoped generator rejected by its oracle: " ++ show failure) False

genIllScopedTerm :: Gen NamedTerm
genIllScopedTerm =
  oneof
    [ NamedHyp <$> elements ["missing", "unbound", "z"]
    , do
        formula <- genKernelFormula 2
        bodyFormula <- genKernelFormula 1
        name <- elements ["h", "x", "v"]
        pure (NamedLam (Just name) formula (NamedLam (Just name) bodyFormula (NamedHyp name)))
    ]

prop_illScopedTermsMatchOracle :: Property
prop_illScopedTermsMatchOracle =
  forAll genIllScopedTerm $ \term ->
    let payload = renderNamedTerm term
     in case referenceLower [] term of
          Left expected ->
            counterexample ("ill-scoped term: " ++ show term) $
              lowerNamedPayload (resolverFrom namedResolver) namedPremiseCount payload === Left expected
          Right _ -> counterexample "ill-scoped generator unexpectedly translated" False

prop_kernelHypInjectedIntoNamedTermIsRejected :: Property
prop_kernelHypInjectedIntoNamedTermIsRejected =
  forAll genWellScopedNamedTerm $ \term ->
    let payload = app (hyp "0") (renderNamedTerm term)
     in counterexample ("payload: " ++ show payload) $
          lowerNamedPayload (resolverFrom namedResolver) namedPremiseCount payload === Left ("0", NamedKernelIndex)

renameOuterBinderToPremise :: NamedTerm -> NamedTerm
renameOuterBinderToPremise (NamedLam (Just _) formula body) = NamedLam (Just "a") formula body
renameOuterBinderToPremise term = term

genNamedLam :: Gen NamedTerm
genNamedLam = sized $ \n -> do
  formula <- genKernelFormula (n `div` 3)
  body <- resize (max 0 (n - 1)) genWellScopedNamedTerm
  pure (NamedLam (Just "binder") formula body)

prop_premiseNameBinderIsRejected :: Property
prop_premiseNameBinderIsRejected =
  forAll genNamedLam $ \term ->
    let renamed = renameOuterBinderToPremise term
        payload = renderNamedTerm renamed
     in counterexample ("renamed term: " ++ show renamed) $
          lowerNamedPayload (resolverFrom namedResolver) namedPremiseCount payload === Left ("a", NamedBinderShadowsPremise)

-- The integration vectors deliberately start from S1: its policy has exactly
-- one premise slot, so @e1@ is hand-checked to lower to @0@.
s1Program :: String -> IO String
s1Program payload = do
  source <- readFile "examples/S1/example.lara"
  pure (replaceFirst "(hyp 0)" payload source)

s1Policy :: IO String
s1Policy = readFile "examples/S1/strict-v1.policy.lara"

replaceFirst :: String -> String -> String -> String
replaceFirst needle replacement = go
  where
    go [] = []
    go rest@(c : cs)
      | needle `isPrefixOf` rest = replacement ++ drop (length needle) rest
      | otherwise = c : go cs

parseS1 :: String -> IO (Either String (Program, Policy))
parseS1 payload = do
  programSource <- s1Program payload
  policySource <- s1Policy
  pure $ do
    program <- either (Left . show) Right (parseProgram programSource)
    policy <- either (Left . show) Right (parsePolicy policySource)
    Right (program, policy)

elaborateS1 :: String -> IO (Either String Unit)
elaborateS1 payload = do
  parsed <- parseS1 payload
  pure $ do
    (program, policy) <- parsed
    either (Left . elabErrorMessage) Right (elaborate (registryOf policy) program policy)

sourceVerdictS1 :: String -> IO (Either String Verdict)
sourceVerdictS1 payload = do
  parsed <- parseS1 payload
  pure $ do
    (program, policy) <- parsed
    case prepareSource program policy of
      Left invalid -> Left (show invalid)
      Right SourceRejected{} -> Left "unexpected admission rejection"
      Right (SourceAccepted input) -> Right (sourceResultVerdict (runSourceCheck input))

prop_s1NamedPremiseTwin :: Property
prop_s1NamedPremiseTwin = once $ ioProperty $ do
  named <- elaborateS1 "(prem e1)"
  numeric <- elaborateS1 "(hyp 0)"
  pure $ case (named, numeric) of
    (Right a, Right b) ->
      counterexample "(prem e1) did not lower to S1's numeric Unit bytes" $
        printSExpr (encodeUnit a) === printSExpr (encodeUnit b)
    (Left err, _) -> counterexample err False
    (_, Left err) -> counterexample err False

prop_s1NamedBinderTwin :: Property
prop_s1NamedBinderTwin = once $ ioProperty $ do
  let namedPayload = "(app (lam h <F> (hyp h)) (prem e1))"
      numericPayload = "(app (lam <F> (hyp 0)) (hyp 0))"
  namedUnit <- elaborateS1 namedPayload
  numericUnit <- elaborateS1 numericPayload
  namedVerdict <- sourceVerdictS1 namedPayload
  numericVerdict <- sourceVerdictS1 numericPayload
  pure $ case (namedUnit, numericUnit, namedVerdict, numericVerdict) of
    (Right a, Right b, Right v1, Right v2) ->
      conjoin
        [ counterexample "named binder Unit bytes drifted" (printSExpr (encodeUnit a) === printSExpr (encodeUnit b))
        , counterexample "named binder verdict bytes drifted" (printSExpr (encodeVerdict v1) === printSExpr (encodeVerdict v2))
        ]
    (Left err, _, _, _) -> counterexample err False
    (_, Left err, _, _) -> counterexample err False
    (_, _, Left err, _) -> counterexample err False
    (_, _, _, Left err) -> counterexample err False

prop_theoryReferenceMatchesKernelLayout :: Property
prop_theoryReferenceMatchesKernelLayout = once $
  case lowerNamedPayload rho 1 (thy "0") of
    Left err -> counterexample ("theory reference did not lower: " ++ show err) False
    Right lowered ->
      conjoin
        [ counterexample "(thy 0) did not lower after the premise context" $
            lowered === hyp "1"
        , case (check lowered, check (hyp "1")) of
            (Right namedJudgment, Right numericJudgment) ->
              conjoin
                [ counterexample "named and numeric theory references replayed differently" $
                    namedJudgment === numericJudgment
                , counterexample "theory reference reported the wrong dependency" $
                    Strict.sjDependencies namedJudgment === Set.singleton (Strict.TheoryEntry 0)
                ]
            (Left err, _) -> counterexample ("lowered theory reference rejected: " ++ show err) False
            (_, Left err) -> counterexample ("numeric theory reference rejected: " ++ show err) False
        , case lowerNamedPayload rho 1 (thy "99") of
            Left err -> counterexample ("unbounded theory reference failed during lowering: " ++ show err) False
            Right outOfRange ->
              conjoin
                [ counterexample "(thy 99) lowered to the wrong free index" $
                    outOfRange === hyp "100"
                , case check outOfRange of
                    Left (Strict.BackendRejected backend reason) ->
                      conjoin
                        [ backend === ND.ndBackendId
                        , counterexample reason $
                            property ("free de Bruijn index out of range: hyp 100" `isInfixOf` reason)
                        ]
                    Left err -> counterexample ("unexpected strict error: " ++ show err) False
                    Right _ -> counterexample "out-of-range theory reference replayed" False
                ]
        ]
  where
    digest = Strict.TheoryDigest "named-theory"
    premise = Prop (Pred "premise") []
    theory = Prop (Pred "theory") []
    registry = Strict.mkRegistry [ND.mkNDBackend [(digest, [theory])]]
    check = Strict.strictCheck registry ND.ndBackendId digest [premise] theory

-- These literals are the public templates, independently of the lowering
-- implementation. A missing dispatch leaves every row as an unexpected
-- successful elaboration, proving this test protects the integration seam.
prop_namedErrorMessages :: Property
prop_namedErrorMessages = once $
  conjoin
    [ exact (CertNdBinderUnbound a b 1 (ArgRef "h")) "arg 'a': certificate 'nd@1' reference 'h' names no enclosing lam binder"
    , exact (CertNdBinderShadowed a b 1 (ArgRef "h")) "arg 'a': certificate 'nd@1' lam binder 'h' shadows an enclosing binder; rename one"
    , exact (CertNdBinderShadowsPremise a b 1 (ArgRef "e1")) "arg 'a': certificate 'nd@1' lam binder 'e1' is also a citable premise name of this instance; rename the binder"
    , exact (CertNdMalformedBinder a b 1 (ArgRef "0")) "arg 'a': certificate 'nd@1' lam binder '0' is not a source identifier"
    , exact (CertNdNonCanonicalIndex a b 1 (ArgRef "007")) "arg 'a': certificate 'nd@1' index '007' is not a canonical index (use unsigned decimal with no leading zeros)"
    , exact (CertNdKernelIndex a b 1 (ArgRef "0")) "arg 'a': certificate 'nd@1' kernel index '0' appears in a named-form payload; cite a binder by name, a premise with (prem ...), or a theory entry with (thy ...)"
    , exact (CertNdPremOutOfRange a b 1 (ArgRef "1") 1 1) "arg 'a': certificate 'nd@1' premise reference '1' names slot 1 but this argument has only 1 premise slot(s)"
    , exact (CertNdResidualNamed a b 1 (ArgRef "e1")) "arg 'a': certificate 'nd@1' named spelling 'e1' sits where the nd@1 grammar gives it no meaning"
    ]
  where
    a = ArgId "a"
    b = AST.BackendId "nd"
    exact err expected = counterexample (show err) (elabErrorMessage err === expected)

prop_namedPremiseUsesCertSlotError :: Property
prop_namedPremiseUsesCertSlotError = once $ ioProperty $ do
  parsed <- parseS1 "(prem missing)"
  pure $ case parsed of
    Left err -> counterexample err False
    Right (program, policy) ->
      case elaborate (registryOf policy) program policy of
        Left err ->
          conjoin
            [ counterexample (show err) $
                property $ case err of
                  CertSlotUnresolved (ArgId "a1") (AST.BackendId "nd") 1 (ArgRef "missing") (RuleId "certified_citation") -> True
                  _ -> False
            , counterexample "certificate-slot wording changed" $
                elabErrorMessage err
                  === "arg 'a1': certificate 'nd@1' premise reference 'missing' names neither a premise label of rule 'certified_citation', a declared leaf, nor a prior argument"
            ]
        Right _ -> counterexample "unresolved named premise elaborated" False

prop_r13Boundary :: Property
prop_r13Boundary = once $ ioProperty $ do
  foo <- sourceVerdictS1 "(foo bar)"
  noncanonical <- sourceVerdictS1 "(hyp 007)"
  fooUnit <- elaborateS1 "(foo bar)"
  noncanonicalUnit <- elaborateS1 "(hyp 007)"
  residual <- elaborateS1 "(foo (prem e1))"
  lowered <- elaborateS1 "(prem e1)"
  parsed <- parseS1 "(prem e1)"
  let tampered = do
        (program, policy) <- parsed
        unit <- lowered
        replayId <- either (Left . show) Right (mkReplayId LaraCoreV02 (AST.policyId policy) (AST.programBackends program) (map fst (AST.policyTheories policy)) (AST.programDigest program))
        tamperedCore <- either (Left . show) Right (parseSExpr (replaceFirst "(hyp 0)" "(hyp 9)" (printSExpr (encodeUnit unit))))
        tamperedUnit <- either (Left . show) Right (decodeUnit tamperedCore)
        input <- either (Left . show) Right (mkCheckInput replayId tamperedUnit)
        Right (sourceResultVerdict (runSourceCheck (case prepareSource program policy of Right (SourceAccepted value) -> value; _ -> error "S1 preparation failed")), runCheck input)
  pure $
    conjoin
      [ rejectsR13 "marker-free payload" foo
      , rejectsR13 "standalone noncanonical hypothesis" noncanonical
      , unchanged "marker-free payload" "(foo bar)" fooUnit
      , unchanged "standalone noncanonical hypothesis" "(hyp 007)" noncanonicalUnit
      , case residual of
          Left err -> counterexample err (property ("named spelling 'e1' sits where the nd@1 grammar gives it no meaning" `isInfixOf` err))
          Right _ -> counterexample "residual named payload elaborated" False
      , case tampered of
          Right (_, verdict) -> counterexample "tampered lowered payload did not reject R13" (verdictOutcome verdict === Reject (RejectClass R13))
          Left err -> counterexample (show err) False
      ]
  where
    rejectsR13 what result = case result of
      Right verdict -> counterexample what (verdictOutcome verdict === Reject (RejectClass R13))
      Left err -> counterexample err False

    unchanged what spelling result = case result of
      Right unit -> counterexample (what ++ " changed during elaboration") $
        property (spelling `isInfixOf` printSExpr (encodeUnit unit))
      Left err -> counterexample err False

prop_namedPrinterRoundTrip :: Property
prop_namedPrinterRoundTrip = once $ ioProperty $ do
  source <- s1Program "(app (lam h <F> (hyp h)) (prem e1))"
  pure $ case parseProgram source of
    Left err -> counterexample (show err) False
    Right program ->
      conjoin
        [ counterexample "named atoms did not round-trip" (parseProgram (printProgram program) === Right program)
        , counterexample "printer erased named atoms" (property ("(lam h <F> (hyp h)) (prem e1)" `isInfixOf` printProgram program))
        ]
