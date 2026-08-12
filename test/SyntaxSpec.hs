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

import Data.List (isInfixOf, nub)
import Test.QuickCheck

import Lara.AST
import Lara.Prop (Prop (..), Term (..))
import Lara.Sigma
  ( ConSig (..)
  , PredSig (..)
  , Sigma (..)
  , Sort (..)
  , SortName (..)
  )
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
  [ "artifact", "policy", "at", "use", "backends", "let", "claim", "leaf", "arg"
  , "status", "rule", "mode", "premises", "conclusion", "question", "contrary"
  , "exception", "admission", "theory", "nl", "formal", "binding", "kind", "provenance"
  , "refs", "author", "rationale", "audit-status", "by", "supports"
  , "challenges", "discharge", "with", "open", "as", "assurance", "rebut", "undercut"
  , "undermine", "allow-trusted", "certifiers", "cert", "trusted", "none"
  , "strict", "defeasible", "observed", "attested", "assumed", "certified"
  , "user", "ai-executed", "checker", "unreviewed", "reviewed", "disputed"
  , "mandatory", "optional", "admit", "quarantine", "reject", "true", "false"
  , "duplicate-reports"
    -- lara-syntax@0.4 (grammar §1.4; Apps. B.7 and C.1). This list MIRRORS
    -- §1.4 and must be kept in sync with it: a keyword missing here lets the
    -- generator emit a colliding identifier, and the round-trip property then
    -- fails for a reason that has nothing to do with the grammar.
  , "measurand", "comparison", "comparison-scheme", "recheck", "bridge"
  , "result", "baseline", "relation", "claims", "on", "where", "cell"
  , "sort", "con", "pred", "Num", "Str"
  , "higher-is-better", "lower-is-better", "strictly-better", "at-least-as-good"
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

-- | A single-line string body with no @\"@ or newline (grammar §1.3). Braces
-- are excluded: they are ordinary characters in a binding @rationale@ but
-- carry the @nl@ contract of App. B.6, so 'genNlStr' builds those separately.
genStr :: Gen String
genStr = listOf (elements (['a' .. 'z'] ++ ['0' .. '9'] ++ " (),.:;=_-/#"))

-- | An @nl@ string body honouring grammar App. B.6's brace contract: plain
-- text, @{cell \<leafId\>}@ directives, one-token @{valueName}@ references,
-- and @{{@\/@}}@ literal-brace escapes. The presentation AST stores the body
-- raw, so every piece here must be reproduced byte-for-byte by the printer.
genNlStr :: Gen String
genNlStr = concat <$> smallListOf piece
  where
    piece =
      frequency
        [ (5, genStr)
        , (3, (\l -> "{cell " ++ l ++ "}") <$> genIdent)
        , (2, (\v -> "{" ++ v ++ "}") <$> genIdent)
        , (2, elements ["{{", "}}"])
        ]

-- | Does an @nl@ body exercise B.6's brace forms at all?
hasBraceForm :: String -> Bool
hasBraceForm s = '{' `elem` s || '}' `elem` s

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

-- | Every claim-form @nl@ uses App. B.6's brace contract.
genClaim :: Gen Claim
genClaim =
  Claim
    <$> (PropId <$> genIdent)
    <*> genNlStr
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

-- | An authored position path (grammar §7, App. B.5): each segment is either an
-- integer ('StepIndex') or a name ('StepName' — a premise label or a question
-- id, which only the elaborator can tell apart). Both spellings must be
-- generated: each round-trips as written, and reconstructing one from the other
-- is exactly what the presentation AST exists to avoid.
genSurfacePath :: Gen [SurfaceStep]
genSurfacePath =
  smallListOf
    ( oneof
        [ StepIndex <$> choose (0, 20)
        , StepName <$> genIdent
        ]
    )

genAttack :: Gen SurfaceAttack
genAttack =
  oneof
    [ SRebut <$> (ArgId <$> genIdent) <*> (ArgId <$> genIdent)
    , SUndercut <$> (ArgId <$> genIdent) <*> (ArgId <$> genIdent) <*> genSurfacePath
    , SUndermine <$> (ArgId <$> genIdent) <*> (ArgId <$> genIdent) <*> genSurfacePath
    ]

-- | Does a declaration carry an attack path segment of the given spelling?
declHasStep :: (SurfaceStep -> Bool) -> Decl -> Bool
declHasStep p d = case d of
  DeclAttack (SUndercut _ _ steps) -> any p steps
  DeclAttack (SUndermine _ _ steps) -> any p steps
  _ -> False

isStepIndex :: SurfaceStep -> Bool
isStepIndex (StepIndex _) = True
isStepIndex _ = False

-- ---------------------------------------------------------------------------
-- Programs
-- ---------------------------------------------------------------------------

-- | A duplicate-report group declaration (grammar §4.3). Round-trip is purely
-- syntactic, so any member list (including empty / singleton) is a legal
-- generator target — R14 well-formedness is the elaborator's job, exercised in
-- "WireSpec" and "ElaborateSpec", not here.
genGroup :: Gen DupGroup
genGroup =
  DupGroup
    <$> (GroupId <$> genIdent)
    <*> smallListOf (LeafId <$> genIdent)

-- | A @comparison@ block (grammar App. B.3). Round-trip is purely syntactic:
-- the 2-arity of the authored conclusion, scheme availability, and every other
-- B.3 precondition are elaborator checks, so any well-shaped surface value is a
-- legal generator target here.
genComparison :: Gen Comparison
genComparison =
  Comparison
    <$> genProp
    <*> (MeasurandId <$> genIdent)
    <*> (DatasetId <$> genIdent)
    <*> elements [StrictlyBetter, AtLeastAsGood]
    <*> (ArgId <$> genIdent)
    <*> (ArgId <$> genIdent)
    <*> (LeafId <$> genIdent)
    <*> (LeafId <$> genIdent)
    <*> (LeafId <$> genIdent)
    <*> genComparisonClaim
    <*> oneof [pure Nothing, Just . PropId <$> genIdent]

genComparisonClaim :: Gen ComparisonClaim
genComparisonClaim =
  ComparisonClaim <$> (PropId <$> genIdent) <*> genNlStr <*> genBinding

genDecl :: Gen Decl
genDecl =
  oneof
    [ DeclClaim <$> genClaim
    , DeclLeaf <$> genLeaf
    , DeclArg <$> genArg
    , DeclAttack <$> genAttack
    , DeclStatus . PropId <$> genIdent
    , DeclGroup <$> genGroup
    , DeclComparison <$> genComparison
    ]

genBackendRef :: Gen (BackendId, String)
genBackendRef = do
  b <- genIdent
  v <- oneof [show <$> (choose (0, 99) :: Gen Int), genIdent]
  pure (BackendId b, v)

genValueBindings :: Gen [ValueBinding]
genValueBindings = do
  names <- nub <$> smallListOf genIdent
  terms <- vectorOf (length names) genTerm
  pure (zipWith (\name term -> ValueBinding (ValueName name) term) names terms)

genProgram :: Gen Program
genProgram = do
  artifact <- genIdent
  digest <- Digest <$> genDigestStr
  policy <- PolicyId <$> genIdent
  backends <- smallListOf genBackendRef
  bindings <- genValueBindings
  decls <- smallListOf genDecl
  pure
    Program
      { programArtifact = artifact
      , programDigest = digest
      , programPolicy = policy
      , programBackends = backends
      , programValueBindings = bindings
      , programDecls = decls
      }

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
  labels <-
    genPremiseLabels [q | Question (QuestionId q) _ _ <- qs] (length prems)
  pure
    Rule
      { ruleId = rid
      , ruleParams = params
      , ruleMode = mode
      , rulePremises = prems
      , rulePremiseLabels = labels
      , ruleConclusion = concl
      , ruleAllowTrusted = at
      , ruleCertifiers = certs
      , ruleQuestions = qs
      }

-- | Optional premise labels for a rule with @n@ premises (grammar App. B.4).
--
-- Two generator constraints, both mirroring what the parser accepts:
--
--   * the canonical unlabelled value is @[]@ — a non-empty all-'Nothing' list
--     prints as the unlabelled spelling and so re-parses to @[]@, which would
--     be a value the printer cannot faithfully render;
--   * labels must be pairwise distinct, disjoint from the rule's question ids,
--     and never @rule@\/@leaf@ — those are declaration-time parse errors,
--     rejected because they would make an attack path ambiguous.
--
-- Both are enforced by construction rather than by @suchThat@, so the generator
-- never discards.
genPremiseLabels :: [String] -> Int -> Gen [Maybe PremiseLabel]
genPremiseLabels questionIds n
  | n <= 0 = pure []
  | otherwise = do
      keeps <- vectorOf n (elements [True, False])
      if not (or keeps)
        then pure []
        else do
          raws <- vectorOf n genIdent
          pure (assign (questionIds ++ ["rule", "leaf"]) (zip keeps raws))
  where
    assign _ [] = []
    assign used ((keep, raw) : rest)
      | not keep = Nothing : assign used rest
      | otherwise =
          let l = freshen used raw
           in Just (PremiseLabel l) : assign (l : used) rest
    freshen used l = if l `elem` used then freshen used (l ++ "_") else l

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
  gm <- elements [QuarantineOnConflict, RejectOnConflict]
  ms <- genMeasurands
  schs <- genSchemes
  sg <- genSigma
  pure
    Policy
      { policyId = pid
      , policySigma = sg
      , policyRules = rs
      , policyContraries = cs
      , policyExceptions = es
      , policyAdmission = adm
      , policyTheories = ts
      , policyGroupMode = gm
      , policyMeasurands = ms
      , policyComparisonSchemes = schs
      }

-- | The measurand table (grammar App. B.1). Ids are index-derived because a
-- duplicate measurand is a parse error — the same construction the theory-digest
-- generator above uses for the same reason.
genMeasurands :: Gen [Measurand]
genMeasurands = do
  k <- choose (0, 3 :: Int)
  pols <- vectorOf k (elements [HigherIsBetter, LowerIsBetter])
  pure
    [ Measurand (MeasurandId ("measurand_" ++ show i)) SortNum (Just pol)
    | (i, pol) <- zip [0 :: Int ..] pols
    ]

-- | The policy signature blocks (grammar §4.0, @lara-core\@0.2@). Sort,
-- constructor, and predicate names are index-derived so a generated policy is
-- duplicate-free — duplicates are Σ-well-formedness (checker R2), not a parse
-- error, but a generator that produced them would still be printing something
-- no author would write.
--
-- Sorts include the two base spellings so a signature that mentions @Num@ and
-- one that mentions a declared name both round-trip.
genSigma :: Gen Sigma
genSigma = do
  nSorts <- choose (0, 3 :: Int)
  let sorts = [SortName ("Sort" ++ show i) | i <- [0 .. nSorts - 1]]
      genSort =
        if null sorts
          then elements [SortNum, SortStr]
          else oneof [elements [SortNum, SortStr], SortDecl <$> elements sorts]
      resultSort = if null sorts then elements [SortNum, SortStr] else genSort
  nCons <- choose (0, 3 :: Int)
  cons <-
    sequence
      [ ConSig (FunSym ("con_" ++ show i))
          <$> (choose (0, 2 :: Int) >>= \k -> vectorOf k genSort)
          <*> resultSort
      | i <- [0 .. nCons - 1]
      ]
  nPreds <- choose (0, 3 :: Int)
  preds <-
    sequence
      [ PredSig (Pred ("pred_" ++ show i))
          <$> (choose (0, 2 :: Int) >>= \k -> vectorOf k genSort)
      | i <- [0 .. nPreds - 1]
      ]
  pure (Sigma sorts cons preds)

-- | Comparison schemes (grammar App. B.2). Schemes are keyed by the
-- @(relation, polarity)@ pair and a duplicate pair is a parse error, so this
-- draws a sublist of the four possible pairs rather than sampling freely.
genSchemes :: Gen [ComparisonScheme]
genSchemes = do
  pairs <-
    sublistOf
      [ (rel, pol)
      | rel <- [StrictlyBetter, AtLeastAsGood]
      , pol <- [HigherIsBetter, LowerIsBetter]
      ]
  mapM one pairs
  where
    one (rel, pol) =
      ComparisonScheme rel pol
        <$> (RuleId <$> genIdent)
        <*> (RuleId <$> genIdent)

-- ---------------------------------------------------------------------------
-- Result 12 round-trip (the crux)
-- ---------------------------------------------------------------------------

prop_programRoundTrip :: Property
prop_programRoundTrip =
  forAll genProgram $ \p -> parseProgram (printProgram p) === Right p

-- | Empty binding tables retain the exact legacy bytes.
prop_emptyValueBindingsRoundTrip :: Property
prop_emptyValueBindingsRoundTrip =
  once $
    let program = valueBindingFixture []
        source =
          unlines
            [ "artifact binding_fixture at sha256:binding-fixture"
            , "policy binding-policy"
            , "use backends []"
            , ""
            , "status c"
            ]
     in conjoin
          [ printProgram program === source
          , parseProgram source === Right program
          ]

-- | Non-empty tables print in authored order with one blank line before decls.
prop_nonEmptyValueBindingsRoundTrip :: Property
prop_nonEmptyValueBindingsRoundTrip =
  once $
    let bindings =
          [ ValueBinding (ValueName "candidate") (TCon (FunSym "sys_new") [])
          , ValueBinding (ValueName "candidate_score") (TCon (FunSym "box") [TNum "0.74"])
          ]
        program = valueBindingFixture bindings
        source =
          unlines
            [ "artifact binding_fixture at sha256:binding-fixture"
            , "policy binding-policy"
            , "use backends []"
            , "let candidate = sys_new"
            , "let candidate_score = box(0.74)"
            , ""
            , "status c"
            ]
        noDeclProgram = program {programDecls = []}
        noDeclSource =
          unlines
            [ "artifact binding_fixture at sha256:binding-fixture"
            , "policy binding-policy"
            , "use backends []"
            , "let candidate = sys_new"
            , "let candidate_score = box(0.74)"
            ]
     in conjoin
          [ printProgram program === source
          , parseProgram source === Right program
          , printProgram noDeclProgram === noDeclSource
          , parseProgram noDeclSource === Right noDeclProgram
          ]


-- | Inline spaces around a value name are authored bytes, just like the gaps
-- retained by the @{cell …}@ form.
prop_spacedValueReferenceRoundTrip :: Property
prop_spacedValueReferenceRoundTrip =
  once $
    let source =
          unlines
            [ "artifact binding_fixture at sha256:binding-fixture"
            , "policy binding-policy"
            , "use backends []"
            , "let candidate = sys_new"
            , ""
            , "claim c"
            , "  nl = \"selected { \tcandidate \t} from { \tcell\te1 \t}\""
            , "  formal = selected(sys_new)"
            , "  binding = { author = alice, rationale = \"\", audit-status = reviewed }"
            ]
     in case parseProgram source of
          Left err -> counterexample (show err) False
          Right program -> printProgram program === source

valueBindingFixture :: [ValueBinding] -> Program
valueBindingFixture bindings =
  Program
    { programArtifact = "binding_fixture"
    , programDigest = Digest "sha256:binding-fixture"
    , programPolicy = PolicyId "binding-policy"
    , programBackends = []
    , programValueBindings = bindings
    , programDecls = [DeclStatus (PropId "c")]
    }

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

-- ---------------------------------------------------------------------------
-- Coverage: the @0.3 forms are actually generated (eng-review 9A)
-- ---------------------------------------------------------------------------
--
-- Without these the extended round-trip property above passes /vacuously/ for
-- any form the generators silently stopped emitting — a green suite that proves
-- nothing about @lara-syntax\@0.3@. 'checkCoverage' makes each threshold an
-- assertion rather than a printed note; the thresholds sit well under the
-- generators' real rates so they measure presence, not tuning.

-- | Every @0.3 / @0.4 /program/ form reaches the round-trip.
prop_programFormCoverage :: Property
prop_programFormCoverage =
  checkCoverage $
    forAll genProgram $ \p ->
      let ds = programDecls p
       in cover 20 (not (null (programValueBindings p))) "value binding table"
            . cover 5 (any isComparison ds) "comparison block"
            . cover 2 (any (declHasStep isStepIndex) ds) "attack path: StepIndex"
            . cover 2 (any (declHasStep (not . isStepIndex)) ds) "attack path: StepName"
            . cover 5 (any claimNlHasBrace ds) "nl string with value/{cell …}/{{}}"
            $ parseProgram (printProgram p) === Right p
  where
    isComparison (DeclComparison _) = True
    isComparison _ = False
    claimNlHasBrace d = case d of
      DeclComparison c -> hasBraceForm (ccNlRaw (cmpClaim c))
      _ -> False

-- | Every @0.3 /policy/ form reaches the round-trip.
prop_policyFormCoverage :: Property
prop_policyFormCoverage =
  checkCoverage $
    forAll genPolicy $ \p ->
      cover 20 (not (null (policyMeasurands p))) "measurand table"
        . cover 20 (not (null (policyComparisonSchemes p))) "comparison-scheme"
        . cover 20 (any hasLabel (policyRules p)) "labelled rule premises"
        -- The @lara-core\@0.2@ signature blocks (#89 §10). Without these three
        -- the round-trip above would pass vacuously the moment the generator
        -- stopped emitting a signature — the trap the @0.3 surface hit and the
        -- reason this coverage block exists at all. `declared sort in a
        -- signature` is separate from `sort block` because a signature over the
        -- base sorts alone would never exercise the declared-name path.
        . cover 20 (not (null (sigmaSorts (policySigma p)))) "sort block"
        . cover 20 (not (null (sigmaCons (policySigma p)))) "con declarations"
        . cover 20 (not (null (sigmaPreds (policySigma p)))) "pred declarations"
        . cover 10 (usesDeclaredSort p) "declared sort in a signature"
        . cover 5 (any nullarySymbol (sigmaCons (policySigma p))) "nullary constructor"
        $ parsePolicy (printPolicy p) === Right p
  where
    hasLabel r = any (/= Nothing) (rulePremiseLabels r)
    nullarySymbol c = null (conArgs c)
    usesDeclaredSort p =
      any isDeclared (concatMap conArgs (sigmaCons (policySigma p)))
        || any (isDeclared . conResult) (sigmaCons (policySigma p))
        || any isDeclared (concatMap predArgs (sigmaPreds (policySigma p)))
    isDeclared (SortDecl _) = True
    isDeclared _ = False

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
    -- lara-syntax@0.3, grammar App. B.6: the nl brace contract is strict, so a
    -- mistyped directive is a located error and never silent literal text.
  , ( "unknown nl directive"
    , claimProgram "\"the value is {cel e2}\""
    , "unknown nl directive"
    )
  , ( "nl directive missing a leaf id"
    , claimProgram "\"the value is {cell}\""
    , "leaf id"
    )
  , ( "unterminated nl directive"
    , claimProgram "\"the value is {cell e2\""
    , "unterminated"
    )
  , ( "bare closing brace in nl"
    , claimProgram "\"a } b\""
    , "unmatched '}'"
    )
  ]
  where
    assuranceProgram body =
      "artifact a at sha256:aa\npolicy p\nuse backends []\n" ++ body
    -- App. B.6's brace contract applies to §3's ordinary claim form as well as
    -- a comparison block's nested claims form.
    claimProgram nl =
      assuranceProgram $
        "claim c\n"
          ++ "  nl = " ++ nl ++ "\n"
          ++ "  formal = p\n"
          ++ "  binding = { author = alice, audit-status = reviewed }\n"

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
  , ( "bad duplicate-reports mode"
    , "policy p\nduplicate-reports = bogus\n"
    , "group conflict mode"
    )
    -- lara-syntax@0.3, grammar App. B.1/B.2/B.4.
  , ( "duplicate measurand"
    , "policy p\nmeasurand acc : Num where higher-is-better\n"
        ++ "measurand acc : Num where lower-is-better\n"
    , "duplicate measurand"
    )
  , ( "bad measurand polarity"
    , "policy p\nmeasurand acc : Num where bigger\n"
    , "polarity"
    )
    -- The sort slot is open since lara-core@0.2 (#89 D-1): `Real` parses as a
    -- declared sort name. What is NOT open is a polarity clause on a non-Num
    -- measurand, because only Num is ordered.
  , ( "polarity clause on a non-Num measurand"
    , "policy p\nmeasurand acc : Dataset where higher-is-better\n"
    , "polarity clause"
    )
  , ( "duplicate comparison-scheme pair"
    , "policy p\n"
        ++ "comparison-scheme strictly-better higher-is-better\n  recheck = r1\n  bridge = r2\n"
        ++ "comparison-scheme strictly-better higher-is-better\n  recheck = r3\n  bridge = r4\n"
    , "duplicate comparison-scheme"
    )
  , ( "bad comparison-scheme relation"
    , "policy p\ncomparison-scheme sort-of-better higher-is-better\n  recheck = r1\n  bridge = r2\n"
    , "relation"
    )
  , ( "duplicate premise label"
    , "policy p\nrule r()\n  mode = defeasible\n"
        ++ "  premises = [ cmp: a, cmp: b ]\n  conclusion = c\n"
    , "duplicate premise label"
    )
  , ( "premise label collides with a question id"
    , "policy p\nrule r()\n  mode = defeasible\n"
        ++ "  premises = [ q1: a ]\n  conclusion = c\n  question q1 : ans\n"
    , "also names a critical question"
    )
  , ( "premise label spells a terminal marker"
    , "policy p\nrule r()\n  mode = defeasible\n"
        ++ "  premises = [ leaf: a ]\n  conclusion = c\n"
    , "reserved"
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
  , ("syntax empty value-binding table preserves legacy bytes", quickCheckResult prop_emptyValueBindingsRoundTrip)
  , ("syntax non-empty value-binding table round-trip", quickCheckResult prop_nonEmptyValueBindingsRoundTrip)
  , ("syntax spaced value reference round-trip", quickCheckResult prop_spacedValueReferenceRoundTrip)
  , ("syntax arg assurance round-trip", quickCheckResult prop_argAssuranceRoundTrip)
  , ("syntax policy round-trip (result 12)", deepCheck prop_policyRoundTrip)
  , ("syntax @0.3/@0.4 program forms are covered", quickCheckResult prop_programFormCoverage)
  , ("syntax @0.3 policy forms are covered", quickCheckResult prop_policyFormCoverage)
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
