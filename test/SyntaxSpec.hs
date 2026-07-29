-- | Tests for the concrete @.lara@ surface syntax ("Lara.Syntax": parser +
-- label-preserving canonical printer), mirroring the layered structure of
-- "WireSpec".
--
-- Three layers:
--
--   * __Result 12 round-trip (the crux)__ — @parse ∘ print = id@ as a
--     QuickCheck property over generated 'Program' /and/ 'Policy' values. The
--     generators are constrained to the /surface-representable/ subset of the
--     presentation AST (grammar-legal identifiers\/numbers, positional θ,
--     'SLeaf' discharge targets, no @open@ holes — see "Lara.Syntax"'s header):
--     the property is exact @parse (print x) == Right x@, so a value the printer
--     cannot faithfully render must not be generated.
--   * __golden parse tests__ — the three committed example files parse to
--     @Right@, and re-printing then re-parsing is fixed (@parse (print (parse
--     f)) == parse f@): parse is idempotent through the printer on real files.
--     Trivia is not in the AST, so we do /not/ assert @print ∘ parse@ fixed on
--     the authored bytes.
--   * __negatives__ — malformed surface, unknown keyword, unterminated string,
--     a bad attack-target marker, an unterminated @refs@ list, and a missing
--     required field each yield @Left@ a located error.
module SyntaxSpec (syntaxSpecProps) where

import Data.List (isInfixOf)
import Test.QuickCheck

import Lara.AST
import Lara.Prop (Prop (..), Term (..))
import Lara.Strict (SExpr (..))
import Lara.Syntax

-- ---------------------------------------------------------------------------
-- Small generator helpers
-- ---------------------------------------------------------------------------

-- | Bounded list in recursive positions (keeps generated trees linear in size,
-- as "WireSpec"'s @smallListOf@ does).
smallListOf :: Gen a -> Gen [a]
smallListOf g = do
  k <- choose (0, 3 :: Int)
  vectorOf k g

-- | The fixed vocabulary and attack markers, excluded from generated
-- identifiers so a generated id never collides with a keyword position.
reservedWords :: [String]
reservedWords =
  [ "artifact", "policy", "at", "use", "backends", "claim", "leaf", "arg"
  , "status", "rule", "mode", "premises", "conclusion", "question", "contrary"
  , "exception", "admission", "theory", "nl", "formal", "binding", "kind", "provenance"
  , "refs", "author", "rationale", "audit-status", "by", "supports"
  , "challenges", "discharge", "with", "open", "as", "assurance", "rebut", "undercut"
  , "undermine", "allow-trusted", "certifiers", "cert", "trusted", "none"
  , "strict", "defeasible", "observed", "attested", "assumed", "certified"
  , "user", "ai-executed", "checker", "unreviewed", "reviewed", "disputed"
  , "mandatory", "optional", "admit", "quarantine", "reject", "true", "false"
  ]

-- | An @ident@ (grammar §1.3): letter start, then letters\/digits\/@_@; kept
-- clear of the reserved vocabulary. (Hyphens are legal in @ident@ but omitted
-- here to avoid trailing-@-@ shapes; a strict legal subset.)
genIdent :: Gen String
genIdent = do
  n <- choose (0, 5)
  c <- elements ['a' .. 'z']
  cs <- vectorOf n (elements (['a' .. 'z'] ++ ['0' .. '9'] ++ "_"))
  let s = c : cs
  pure (if s `elem` reservedWords then s ++ "x" else s)

-- | A @number@ (grammar §1.3): optional sign, digits, optional fraction. Every
-- shape re-lexes to itself, so 'TNum' round-trips through the surface.
genNumStr :: Gen String
genNumStr = do
  sign <- elements ["", "+", "-"]
  ints <- listOf1 (elements ['0' .. '9'])
  frac <- oneof [pure "", ('.' :) <$> listOf1 (elements ['0' .. '9'])]
  pure (sign ++ ints ++ frac)

-- | A single-line string body with no @\"@ or newline (grammar §1.3).
genStr :: Gen String
genStr = listOf (elements (['a' .. 'z'] ++ ['0' .. '9'] ++ " (),.:;=_-/#"))

-- | A digest\/theory-digest @ident \":\" body@ (grammar §1.3): the shape both a
-- 'Digest' and a 'TheoryDigest' must have to survive their printers.
genDigestStr :: Gen String
genDigestStr = do
  h <- genIdent
  n <- choose (1, 8)
  body <- vectorOf n (elements (['a' .. 'z'] ++ ['0' .. '9'] ++ "._-"))
  pure (h ++ ":" ++ body)

-- | A source reference: non-empty, no comma\/bracket\/whitespace, @#@ allowed
-- (ref-list mode, grammar §1.2).
genSourceRef :: Gen String
genSourceRef = do
  n <- choose (1, 10)
  vectorOf n (elements (['a' .. 'z'] ++ ['0' .. '9'] ++ "#=._-/"))

-- ---------------------------------------------------------------------------
-- Terms, propositions, patterns
-- ---------------------------------------------------------------------------

-- | A surface term: a numeric literal or a constructor. 'TStr' has no surface
-- spelling in a term position, so it is never generated.
genTerm :: Gen Term
genTerm = sized go
  where
    go n
      | n <= 0 =
          oneof
            [ TNum <$> genNumStr
            , (\k -> TCon (FunSym k) []) <$> genIdent
            ]
      | otherwise =
          frequency
            [ (3, go 0)
            , (1, (\k ts -> TCon (FunSym k) ts) <$> genIdent <*> smallListOf (go (n `div` 2)))
            ]

genProp :: Gen Prop
genProp = Prop <$> (Pred <$> genIdent) <*> smallListOf genTerm

-- | A surface pattern. A bare ident is 'PVar' (the parser defers the
-- param-vs-constant call to the elaborator); numeric literals are 'PLit'
-- ('TNum'); applied heads are 'PCon' with at least one sub-pattern. Nullary
-- 'PCon' and 'PLit' of a 'TCon'\/'TStr' have no distinct surface spelling and
-- are not generated.
genPat :: Gen Pat
genPat = sized go
  where
    go n
      | n <= 0 =
          oneof
            [ PVar . Param <$> genIdent
            , PLit . TNum <$> genNumStr
            ]
      | otherwise =
          frequency
            [ (3, go 0)
            , ( 1
              , PCon <$> (FunSym <$> genIdent) <*> (do k <- choose (1, 3); vectorOf k (go (n `div` 2)))
              )
            ]

genAtomPat :: Gen AtomPat
genAtomPat = AtomPat <$> (Pred <$> genIdent) <*> smallListOf genPat

-- ---------------------------------------------------------------------------
-- Leaves, claims
-- ---------------------------------------------------------------------------

genProvenance :: Gen Provenance
genProvenance =
  oneof
    [ pure User
    , pure AiExecuted
    , Checker <$> genIdent <*> genIdent
    ]

genLeaf :: Gen Leaf
genLeaf =
  Leaf
    <$> (LeafId <$> genIdent)
    <*> genProp
    <*> elements [Observed, Attested, Assumed, Certified]
    <*> genProvenance
    <*> smallListOf (SourceRef <$> genSourceRef)

genBinding :: Gen Binding
genBinding =
  Binding
    <$> genIdent
    <*> genStr
    <*> elements [Unreviewed, Reviewed, Disputed]

genClaim :: Gen Claim
genClaim =
  Claim
    <$> (PropId <$> genIdent)
    <*> genStr
    <*> genProp
    <*> genBinding

-- ---------------------------------------------------------------------------
-- Arguments and their surface support terms
-- ---------------------------------------------------------------------------

-- | The argument conclusion: @supports(c)@ (always parsed as 'SupportsClaim';
-- the elaborator downgrades an undeclared target to 'SupportsDerived', so that
-- arm is not generated) or @challenges(…)@.
genArgConcl :: Gen ArgConcl
genArgConcl =
  oneof
    [ SupportsClaim . PropId <$> genIdent
    , Challenges <$> genChallengeTarget
    ]

genChallengeTarget :: Gen ChallengeTarget
genChallengeTarget =
  oneof
    [ ChallengesQuestion <$> (QuestionId <$> genIdent) <*> (ArgId <$> genIdent)
    , ChallengesLeaf . LeafId <$> genIdent
    ]

-- | A surface support term: either @leaf(l)@, or a rule instance with positional
-- θ (parameter names @\"1\"..\"n\"@), no premises, 'SLeaf' discharge targets,
-- no holes, and a surface-representable assurance (see "Lara.Syntax"'s header).
genSupportTerm :: Gen SupportTerm
genSupportTerm =
  oneof
    [ SLeaf . LeafId <$> genIdent
    , do
        r <- genIdent
        terms <- smallListOf genTerm
        let theta = zipWith (\i t -> (Param (show i), t)) [1 :: Int ..] terms
        disch <-
          smallListOf
            ((,) <$> (QuestionId <$> genIdent) <*> (SLeaf . LeafId <$> genIdent))
        assurance <- genAssurance
        pure
          SRule
            { srRule = RuleId r
            , srSubst = theta
            , srPremises = []
            , srDischarge = disch
            , srHoles = []
            , srAssurance = assurance
            }
    ]

genAssurance :: Gen Assurance
genAssurance =
  frequency
    [ (6, pure AssuranceNone)
    , (2, pure AssuranceTrusted)
    , (2, AssuranceCert <$> genCert)
    ]
  where
    genCert =
      Cert
        <$> (BackendId <$> genIdent)
        <*> choose (0, 99)
        <*> (TheoryDigest <$> genDigestStr)
        <*> (SList <$> smallListOf genSExpr)
    genSExpr =
      sized $ \n ->
        if n <= 0
          then SAtom <$> oneof [genIdent, genStr]
          else
            frequency
              [ (3, SAtom <$> oneof [genIdent, genStr])
              , (1, SList <$> smallListOf (resize (n `div` 2) genSExpr))
              ]

genArg :: Gen Arg
genArg = Arg <$> (ArgId <$> genIdent) <*> genArgConcl <*> genSupportTerm

-- ---------------------------------------------------------------------------
-- Attacks
-- ---------------------------------------------------------------------------

-- | A position path: each step is a premise index or a (non-numeric,
-- non-marker) question id (grammar §7).
genPosition :: Gen Position
genPosition =
  smallListOf
    ( oneof
        [ StepPremise <$> choose (0, 20)
        , StepQuestion . QuestionId <$> genIdent
        ]
    )

genAttack :: Gen Attack
genAttack =
  oneof
    [ Rebut <$> (ArgId <$> genIdent) <*> (ArgId <$> genIdent)
    , Undercut <$> (ArgId <$> genIdent) <*> (ArgId <$> genIdent) <*> genPosition
    , Undermine <$> (ArgId <$> genIdent) <*> (ArgId <$> genIdent) <*> genPosition
    ]

-- ---------------------------------------------------------------------------
-- Programs
-- ---------------------------------------------------------------------------

genDecl :: Gen Decl
genDecl =
  oneof
    [ DeclClaim <$> genClaim
    , DeclLeaf <$> genLeaf
    , DeclArg <$> genArg
    , DeclAttack <$> genAttack
    , DeclStatus . PropId <$> genIdent
    ]

genBackendRef :: Gen (BackendId, String)
genBackendRef = do
  b <- genIdent
  v <- oneof [show <$> (choose (0, 99) :: Gen Int), genIdent]
  pure (BackendId b, v)

genProgram :: Gen Program
genProgram =
  Program
    <$> genIdent
    <*> (Digest <$> genDigestStr)
    <*> (PolicyId <$> genIdent)
    <*> smallListOf genBackendRef
    <*> smallListOf genDecl

-- ---------------------------------------------------------------------------
-- Policy
-- ---------------------------------------------------------------------------

genCertRef :: Gen CertRef
genCertRef =
  CertRef
    <$> (BackendId <$> genIdent)
    <*> choose (0, 99)
    <*> (TheoryDigest <$> genDigestStr)

genQuestion :: Gen Question
genQuestion =
  Question
    <$> (QuestionId <$> genIdent)
    <*> genAtomPat
    <*> elements [Mandatory, Optional]

-- | A rule. @allow-trusted@\/@certifiers@ are a strict-rule surface (grammar
-- §4); a defeasible rule carries neither, so the printer omits them and the
-- generator must leave them at their defaults for the round-trip to hold.
genRule :: Gen Rule
genRule = do
  rid <- RuleId <$> genIdent
  params <- smallListOf (Param <$> genIdent)
  mode <- elements [Strict, Defeasible]
  prems <- smallListOf genAtomPat
  concl <- genAtomPat
  (at, certs) <- case mode of
    Strict -> (,) <$> arbitrary <*> smallListOf genCertRef
    Defeasible -> pure (False, [])
  qs <- smallListOf genQuestion
  pure
    Rule
      { ruleId = rid
      , ruleParams = params
      , ruleMode = mode
      , rulePremises = prems
      , ruleConclusion = concl
      , ruleAllowTrusted = at
      , ruleCertifiers = certs
      , ruleQuestions = qs
      }

genContrary :: Gen Contrary
genContrary = Contrary <$> genAtomPat <*> genAtomPat

genException :: Gen Exception
genException = Exception <$> (RuleId <$> genIdent) <*> genAtomPat

genAdmissionRow :: Gen ((LeafKind, Provenance), Admission)
genAdmissionRow =
  (,)
    <$> ((,) <$> elements [Observed, Attested, Assumed, Certified] <*> genProvenance)
    <*> elements [Admit, Quarantine, Reject]

genPolicy :: Gen Policy
genPolicy = do
  pid <- PolicyId <$> genIdent
  rs <- smallListOf genRule
  cs <- smallListOf genContrary
  es <- smallListOf genException
  adm <- smallListOf genAdmissionRow
  theoryCount <- choose (0, 3)
  theoryProps <- vectorOf theoryCount (smallListOf genProp)
  let ts =
        [ (TheoryDigest ("sha256:theory-" ++ show i), ps)
        | (i, ps) <- zip [0 :: Int ..] theoryProps
        ]
  pure
    Policy
      { policyId = pid
      , policyRules = rs
      , policyContraries = cs
      , policyExceptions = es
      , policyAdmission = adm
      , policyTheories = ts
      }

-- ---------------------------------------------------------------------------
-- Result 12 round-trip (the crux)
-- ---------------------------------------------------------------------------

prop_programRoundTrip :: Property
prop_programRoundTrip =
  forAll genProgram $ \p -> parseProgram (printProgram p) === Right p

prop_argAssuranceRoundTrip :: Property
prop_argAssuranceRoundTrip =
  let src =
        unlines
          [ "artifact paper_42 at sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
          , "policy strict-v1"
          , "use backends [nd@1]"
          , ""
          , "claim c1"
          , "  nl = \"The safety invariant holds for deployment D\""
          , "  formal = holds(safety_invariant, D)"
          , "  binding = { author = alice, rationale = \"r\", audit-status = reviewed }"
          , ""
          , "leaf e1 : holds(safety_invariant, D)"
          , "  kind = attested"
          , "  provenance = user"
          , "  refs = [evidence/safety_audit.txt#section=invariants]"
          , ""
          , "arg a1 : supports(c1) by certified_citation(safety_invariant, D)"
          , "  assurance = cert(nd@1, sha256:strict-v1-theory-0, (hyp 0))"
          , ""
          , "status c1"
          ]
   in case parseProgram src of
        Left e -> counterexample ("parse failed: " ++ show e) False
        Right prog ->
          counterexample "round-trip" $
            parseProgram (printProgram prog) === Right prog

prop_policyRoundTrip :: Property
prop_policyRoundTrip =
  forAll genPolicy $ \p -> parsePolicy (printPolicy p) === Right p

prop_policyTheoriesRoundTrip :: Property
prop_policyTheoriesRoundTrip =
  let src =
        unlines
          [ "policy strict-v1"
          , "rule certified_citation(X, D)"
          , "  mode = strict"
          , "  premises = [ holds(X, D) ]"
          , "  conclusion = holds(X, D)"
          , "  allow-trusted = false"
          , "  certifiers = [ (nd@1, sha256:strict-v1-theory-0) ]"
          , "theory sha256:strict-v1-theory-0 = []"
          ]
   in case parsePolicy src of
        Left e -> counterexample ("parse failed: " ++ show e) False
        Right pol ->
          conjoin
            [ counterexample "round-trip" $
                parsePolicy (printPolicy pol) === Right pol
            , counterexample "theories" $
                policyTheories pol
                  === [(TheoryDigest "sha256:strict-v1-theory-0", [])]
            ]

-- | The keyword-dispatch entry ('parseSource') round-trips both top-levels.
prop_sourceRoundTrip :: Property
prop_sourceRoundTrip =
  forAll (oneof [SourceProgram <$> genProgram, SourcePolicy <$> genPolicy]) $ \s ->
    parseSource (printSource s) === Right s

-- ---------------------------------------------------------------------------
-- Golden parse tests (the three committed example files)
-- ---------------------------------------------------------------------------

-- | Each example file parses to @Right@, and parse is idempotent through the
-- printer (@parse (print (parse f)) == parse f@).
prop_goldenPrograms :: Property
prop_goldenPrograms = once $ ioProperty $ do
  a <- readFile "examples/A/example.lara"
  b <- readFile "examples/B/example.lara"
  pure $
    conjoin
      [ counterexample "A parses" (isRight (parseProgram a))
      , counterexample "B parses" (isRight (parseProgram b))
      , counterexample "A idempotent-through-printer" (idemProgram a)
      , counterexample "B idempotent-through-printer" (idemProgram b)
      ]
  where
    idemProgram src = case parseProgram src of
      Right p -> parseProgram (printProgram p) == Right p
      Left _ -> False

prop_goldenPolicy :: Property
prop_goldenPolicy = once $ ioProperty $ do
  p <- readFile "examples/A/empirical-v1.policy.lara"
  pure $
    conjoin
      [ counterexample "policy parses" (isRight (parsePolicy p))
      , counterexample "policy idempotent-through-printer" (idem p)
      ]
  where
    idem src = case parsePolicy src of
      Right pol -> parsePolicy (printPolicy pol) == Right pol
      Left _ -> False

-- | The leading-keyword dispatch classifies the real files correctly.
prop_goldenSourceDispatch :: Property
prop_goldenSourceDispatch = once $ ioProperty $ do
  a <- readFile "examples/A/example.lara"
  p <- readFile "examples/A/empirical-v1.policy.lara"
  pure $
    conjoin
      [ counterexample "artifact → Program" (isProgram (parseSource a))
      , counterexample "policy → Policy" (isPolicy (parseSource p))
      ]
  where
    isProgram (Right (SourceProgram _)) = True
    isProgram _ = False
    isPolicy (Right (SourcePolicy _)) = True
    isPolicy _ = False

-- ---------------------------------------------------------------------------
-- Pinning test: the questionAnswerP necessity-suffix disambiguation
-- ---------------------------------------------------------------------------

-- | Pin the documented 'questionAnswerP' disambiguation ("Lara.Syntax",
-- grammar §4): a trailing @( necessity )@ after a question's answer pattern is
-- ALWAYS the necessity suffix, never the atom's argument list. So
-- @ans (mandatory)@ parses as the /nullary/ pattern @ans@ with necessity
-- 'Mandatory' — not as the unary @ans(mandatory)@ carrying the default
-- necessity. The generators never spell an ident @mandatory@\/@optional@, so
-- the printer round-trip cannot reach this case; pin it explicitly. If the
-- necessity reserved set ever shrinks, this trips here instead of the
-- round-trip silently breaking on a real policy.
prop_questionNecessityPin :: Property
prop_questionNecessityPin =
  case parsePolicy src of
    Left e -> counterexample ("parse failed: " ++ show e) (property False)
    Right pol -> case concatMap ruleQuestions (policyRules pol) of
      [q] ->
        counterexample ("parsed question was: " ++ show q) $
          conjoin
            [ questionAnswer q === AtomPat (Pred "ans") []
            , questionNecessity q === Mandatory
            ]
      qs -> counterexample ("expected exactly one question, got: " ++ show qs) (property False)
  where
    src =
      "policy pin-test\n"
        ++ "rule r()\n"
        ++ "  mode = defeasible\n"
        ++ "  premises = []\n"
        ++ "  conclusion = c\n"
        ++ "  question cq : ans (mandatory)\n"

-- ---------------------------------------------------------------------------
-- Negatives (each yields Left a located error)
-- ---------------------------------------------------------------------------

-- | (label, source, expected reason substring) for programs that must fail.
programNegatives :: [(String, String, String)]
programNegatives =
  [ ("empty source", "", "artifact")
  , ("unknown leading keyword", "widget foo at sha256:aa", "artifact")
  , ( "unknown decl keyword"
    , "artifact a at sha256:aa\npolicy p\nuse backends []\nblah x\n"
    , "end of input"
    )
  , ( "unterminated string"
    , "artifact a at sha256:aa\npolicy p\nuse backends []\n"
        ++ "claim c\n  nl = \"unterminated\n  formal = q\n"
    , "unterminated string"
    )
  , ( "bad attack marker"
    , "artifact a at sha256:aa\npolicy p\nuse backends []\n"
        ++ "undercut d1 a1.bogus\n"
    , "terminal '.rule'"
    )
  , ( "attack missing marker"
    , "artifact a at sha256:aa\npolicy p\nuse backends []\n"
        ++ "undermine d1 a1\n"
    , "position"
    )
  , ( "unterminated refs list"
    , "artifact a at sha256:aa\npolicy p\nuse backends []\n"
        ++ "leaf e : p\n  kind = observed\n  provenance = user\n  refs = [a.csv\n"
    , "']'"
    )
  , ( "missing required binding field"
    , "artifact a at sha256:aa\npolicy p\nuse backends []\n"
        ++ "claim c\n  nl = \"x\"\n  formal = q\n  binding = { author = alice }\n"
    , "audit-status"
    )
  , ( "missing formal field"
    , "artifact a at sha256:aa\npolicy p\nuse backends []\n"
        ++ "claim c\n  nl = \"x\"\n  binding = { author = a, audit-status = reviewed }\n"
    , "formal"
    )
  , ( "duplicate assurance line"
    , assuranceProgram
        "arg a : supports(c) by r()\n"
        ++ "  assurance = none\n"
        ++ "  assurance = trusted\n"
    , "duplicate assurance"
    )
  , ( "assurance on bare leaf"
    , assuranceProgram
        "arg a : supports(c) by leaf(e)\n"
        ++ "  assurance = trusted\n"
    , "bare leaf"
    )
  , ( "unknown assurance"
    , assuranceProgram
        "arg a : supports(c) by r()\n"
        ++ "  assurance = maybe\n"
    , "expected an assurance"
    )
  , ( "non-parenthesised certificate payload"
    , assuranceProgram
        "arg a : supports(c) by r()\n"
        ++ "  assurance = cert(nd@1, sha256:t, hyp)\n"
    , "parenthesised S-expression"
    )
  , ( "unterminated certificate payload"
    , assuranceProgram
        "arg a : supports(c) by r()\n"
        ++ "  assurance = cert(nd@1, sha256:t, (hyp 0"
    , "unterminated certificate payload"
    )
  , ( "malformed certificate payload"
    , assuranceProgram
        "arg a : supports(c) by r()\n"
        ++ "  assurance = cert(nd@1, sha256:t, (hyp \"bad\\q\"))\n"
    , "malformed certificate payload"
    )
  ]
  where
    assuranceProgram body =
      "artifact a at sha256:aa\npolicy p\nuse backends []\n" ++ body

policyNegatives :: [(String, String, String)]
policyNegatives =
  [ ("unknown policy decl", "policy p\nwidget x\n", "end of input")
  , ( "rule missing conclusion"
    , "policy p\nrule r()\n  mode = defeasible\n  premises = []\n  question q : a\n"
    , "conclusion"
    )
  , ( "bad mode"
    , "policy p\nrule r()\n  mode = bogus\n  premises = []\n  conclusion = a\n"
    , "mode"
    )
  , ( "duplicate theory digest"
    , "policy p\ntheory sha256:t = []\ntheory sha256:t = []\n"
    , "duplicate theory digest"
    )
  , ( "theory missing equals"
    , "policy p\ntheory sha256:t []\n"
    , "'='"
    )
  , ( "unterminated theory list"
    , "policy p\ntheory sha256:t = [p\n"
    , "']'"
    )
  , ( "malformed theory digest"
    , "policy p\ntheory sha256 = []\n"
    , "':'"
    )
  ]

prop_programNegatives :: Property
prop_programNegatives =
  conjoin
    [ counterexample lbl (leftWith reason (parseProgram src))
    | (lbl, src, reason) <- programNegatives
    ]

prop_policyNegatives :: Property
prop_policyNegatives =
  conjoin
    [ counterexample lbl (leftWith reason (parsePolicy src))
    | (lbl, src, reason) <- policyNegatives
    ]

-- | Located errors carry a plausible 1-based position (line ≥ 1, column ≥ 1).
prop_errorsAreLocated :: Property
prop_errorsAreLocated =
  conjoin
    [ counterexample lbl (located (parseProgram src))
    | (lbl, src, _) <- programNegatives
    ]
  where
    located (Left (ParseError l c _)) = l >= 1 && c >= 1
    located (Right _) = False

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight _ = False

-- | Assert a parse failed with a reason mentioning the given substring.
leftWith :: String -> Either ParseError a -> Bool
leftWith needle e = case e of
  Left (ParseError _ _ reason) -> needle `isInfixOf` reason
  Right _ -> False

-- ---------------------------------------------------------------------------
-- Exported runner
-- ---------------------------------------------------------------------------

-- | Run a property at a raised success target (the round-trip crux earns the
-- extra coverage; the generators are cheap).
deepCheck :: (Testable p) => p -> IO Result
deepCheck = quickCheckWithResult stdArgs {maxSuccess = 2000}

syntaxSpecProps :: [(String, IO Result)]
syntaxSpecProps =
  [ ("syntax program round-trip (result 12)", deepCheck prop_programRoundTrip)
  , ("syntax arg assurance round-trip", quickCheckResult prop_argAssuranceRoundTrip)
  , ("syntax policy round-trip (result 12)", deepCheck prop_policyRoundTrip)
  , ("syntax policy theory table round-trip", quickCheckResult prop_policyTheoriesRoundTrip)
  , ("syntax source round-trip", deepCheck prop_sourceRoundTrip)
  , ("syntax golden programs (A, B) parse + idempotent", quickCheckResult prop_goldenPrograms)
  , ("syntax golden policy parse + idempotent", quickCheckResult prop_goldenPolicy)
  , ("syntax golden source dispatch", quickCheckResult prop_goldenSourceDispatch)
  , ("syntax question necessity-suffix disambiguation (pin)", quickCheckResult prop_questionNecessityPin)
  , ("syntax program negatives are located Left", quickCheckResult prop_programNegatives)
  , ("syntax policy negatives are located Left", quickCheckResult prop_policyNegatives)
  , ("syntax parse errors are located", quickCheckResult prop_errorsAreLocated)
  ]
