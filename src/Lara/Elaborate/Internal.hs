-- | The structural surface elaborator, __without__ the source-admission
-- boundary that wraps it.
--
-- == Why this module is @.Internal@
--
-- 'elaborate' lowers a presentation 'Program' + 'Policy' to a checker 'Unit'
-- using __every declared leaf__ (the all-admit context). It deliberately does
-- not read @policyAdmission@: admission is a source-boundary decision, and the
-- boundary lives in "Lara.Elaborate" ('Lara.Elaborate.prepareSource' /
-- 'Lara.Elaborate.runSourceCheck'), which runs the R8 stop, builds the policy
-- quarantine seed, and binds the resulting prune to the replay identity so the
-- three cannot be paired independently.
--
-- So a caller who reaches this function directly and then hands the 'Unit' to
-- @mkCheckInput@ + @runCheck@ obtains a verdict on material the policy
-- rejected or quarantined. That path is not part of the public API: the
-- presentation front door is 'Lara.Elaborate.prepareSource'. This module is the
-- __sanctioned escape hatch__ for tests and golden generators that need the
-- pre-admission lowering itself as their object of study (the same role
-- "Lara.Strict.ND.Internal" plays for 'Lara.Strict.ND.AtomId'). Production code
-- must not import it.
--
-- == The three sibling modules
--
-- The elaborator is split so the @lara-syntax\@0.3@ surface work and the
-- structural lowering can share a failure vocabulary:
--
--   * "Lara.Elaborate.Error" — 'ElabError' and its renderer (re-exported here);
--   * "Lara.Elaborate.Subst" — pattern instantiation and one-way matching;
--   * "Lara.Elaborate.Comparison" — the @comparison@ expansion and @nl@
--     interpolation, a presentation-to-presentation pass this module runs
--     first.
module Lara.Elaborate.Internal
  ( -- * Caller-supplied environment inputs
    Sigma (..)
  , emptySigma
  , defeasibleSuiteSigma
  , TheoryRegistry (..)
  , emptyRegistry
  , registryOf
    -- * Elaboration errors (located-ish: they name the arg/rule/leaf/claim)
    --
    -- | Defined in "Lara.Elaborate.Error" and re-exported here, so that module
    -- and "Lara.Elaborate.Comparison" can raise the same failures without an
    -- import cycle; every existing importer of this module is unaffected.
  , ElabError (..)
  , elabErrorMessage
    -- * The elaborator (admission-free; see the module header)
  , elaborate
  , elaborateWithProvenance
  , GeneratedArg (..)
  ) where

import Control.Monad (foldM, when)
import Data.List (find)

import Lara.AST
import Lara.Elaborate.Comparison (GeneratedArg (..), expandSurfaceProvenance)
import Lara.Elaborate.Error (ElabError (..), elabErrorMessage)
import Lara.Elaborate.Subst (apatToProp)
import Lara.Syntax (attackPathTerminalMarkers)
import Lara.Prop (Prop, equiv)

-- ---------------------------------------------------------------------------
-- Caller-supplied environment inputs
-- ---------------------------------------------------------------------------

-- | The proposition signature @Σ@ (spec §2): predicate arities. In v0.1 Σ-arity
-- checking (rejection class R2) is __outside the executable core__ (plan A1,
-- "Before You Begin"), so the elaborator carries Σ for shape only and performs
-- __no__ arity check against it. The field exists so a future signature pass has
-- one place to read from without changing this function's type.
newtype Sigma = Sigma {sigmaArities :: [(Pred, Int)]}
  deriving (Eq, Show)

-- | The empty signature (no declared arities). Identical to
-- 'defeasibleSuiteSigma' in v0.1 since Σ is not consulted.
emptySigma :: Sigma
emptySigma = Sigma []

-- | The signature for the defeasible worked-examples suite. No arity is checked
-- (R2 is outside the executable core), so this is the empty signature; it exists
-- as the sanctioned default the A/B tests pass.
defeasibleSuiteSigma :: Sigma
defeasibleSuiteSigma = emptySigma

-- | The closed backend-registry theory table (the @nd\@1@ theories, spec §5).
-- For the defeasible-only suite this is empty (@nd\@1@ is inert).
newtype TheoryRegistry = TheoryRegistry {registryTheories :: [(TheoryDigest, [Prop])]}
  deriving (Eq, Show)

-- | The empty theory registry (the defeasible-suite default).
emptyRegistry :: TheoryRegistry
emptyRegistry = TheoryRegistry []

-- | The theory registry a policy declares (lara-syntax@0.2, grammar App. A.2).
-- Every caller that elaborates against a parsed policy should pass
-- @registryOf pol@ instead of 'emptyRegistry' so the policy's theory table
-- reaches 'unitTheories'.
registryOf :: Policy -> TheoryRegistry
registryOf = TheoryRegistry . policyTheories

-- ---------------------------------------------------------------------------
-- Internal environment
-- ---------------------------------------------------------------------------

-- | The read-only elaboration environment, assembled once from the program and
-- policy before any argument is lowered.
data Env = Env
  { envPolicy :: Policy
  , envGamma :: [(LeafId, Prop)] -- ^ Γ: all declared leaves (all-admit default)
  , envClaims :: [Claim]
  , envLeafIds :: [LeafId]
  , envArgIds :: [ArgId]
  }

-- ---------------------------------------------------------------------------
-- The elaborator
-- ---------------------------------------------------------------------------

-- | Lower a parsed 'Program' against its 'Policy' to the checker 'Unit'.
--
-- __Admission-free__: see the module header. The presentation front door is
-- 'Lara.Elaborate.prepareSource'.
--
-- Field-by-field (plan A1b):
--
--   * @unitRules\/unitContraries\/unitExceptions@ pass through from the policy
--     (@checkUnit@ validates policy well-formedness incl. R12);
--   * @unitTheories@ from the registry (empty for the defeasible suite);
--   * @unitLeaves@ (Γ) = every declared leaf — __the structural all-admit
--     context__ the source boundary then prunes with the policy seed; an
--     undeclared leaf reference is left for @checkUnit@ to reject as R1 (kept
--     distinct from the source-boundary R8 admission class);
--   * @unitArgs@ in declaration order (order fixes AF node indices, hence labels);
--     each shallow support term is rebuilt to the full 'SupportTerm';
--   * @unitAttacks@ resolved from the authored 'SurfaceAttack's — an integer
--     path segment is a premise slot, a name is resolved against the /targeted
--     rule/ (grammar App. B.5);
--   * @unitQueries@ = the @status@-named claims' formals;
--   * @unitGroups@ = the declared duplicate-report groups (spec §4.3), with
--     @unitGroupMode@ baked from the policy's conflict escalation choice.
--
-- @lara-syntax\@0.3@ inserts one stage ahead of all of that: every
-- @comparison@ block is expanded to the declarations it stands for
-- ('Lara.Elaborate.Comparison.expandSurface') __before__ any id check, any
-- argument is lowered, or any attack path resolves, so an attack on a generated
-- argument resolves against the post-expansion set (App. B.5, eng review F5).
elaborate :: Sigma -> TheoryRegistry -> Program -> Policy -> Either ElabError Unit
elaborate sigma reg prog0 pol0 = fst <$> elaborateWithProvenance sigma reg prog0 pol0

-- | 'elaborate' paired with the @comparison@ expansion's 'GeneratedArg'
-- breadcrumb (plan D5), from the /same/ pass — so a breadcrumb can never
-- describe an argument this 'Unit' does not contain.
--
-- __The breadcrumb cannot reach 'Unit'.__ It is bound here and used nowhere in
-- the 'Unit' record below, whose ten fields are each written from the policy,
-- the registry, or the expanded declaration list. 'elaborate' — the type every
-- pre-D5 caller uses — projects it away, so no existing path can observe it.
-- The @examples\/*\/example.core.sexp@ byte-identity goldens stand as the
-- regression test.
elaborateWithProvenance
  :: Sigma
  -> TheoryRegistry
  -> Program
  -> Policy
  -> Either ElabError (Unit, [GeneratedArg])
elaborateWithProvenance _sigma reg prog0 pol0 = do
  when (programPolicy prog0 /= policyId pol0) $
    Left (PolicyIdMismatch (programPolicy prog0) (policyId pol0))
  -- Reclassify pattern identifiers (grammar §2): the shallow parser records
  -- every bare pattern ident as a 'PVar', but a non-parameter ident is a ground
  -- constant. The checker's premise instantiation ('instAPat') treats an unbound
  -- 'PVar' as failure (R3), so this resolution is mandatory elaborator work.
  let pol = reclassifyPolicy pol0
  -- Policy well-formedness for premise labels (App. B.4), rejected at
  -- declaration time rather than discovered at an attack site. The parser
  -- enforces the same three rules, but a 'Program' built in memory never went
  -- through it, and the disjointness is what makes B.5's name resolution
  -- single-valued.
  validatePremiseLabels (policyRules pol)
  (prog, generated) <- expandSurfaceProvenance pol prog0
  let decls = programDecls prog
      gamma = [(leafId l, leafProp l) | DeclLeaf l <- decls]
      claims = [c | DeclClaim c <- decls]
      argDecls = [a | DeclArg a <- decls]
      surfaceAttacks = [k | DeclAttack k <- decls]
      statusIds = [pid | DeclStatus pid <- decls]
      groups = [g | DeclGroup g <- decls]
      env =
        Env
          { envPolicy = pol
          , envGamma = gamma
          , envClaims = claims
          , envLeafIds = map fst gamma
          , envArgIds = map argId argDecls
          }
  -- Raw ids drive quarantine retention and raw/resolved attack alignment. Make
  -- their uniqueness a front-door invariant before either operation can use an
  -- ambiguous lookup, matching the wire decoder's R14 check.
  case firstDup (envArgIds env) of
    Just aid -> Left (DuplicateArgId aid)
    Nothing -> Right ()
  case find (`notElem` envArgIds env) (concatMap surfaceAttackEndpoints surfaceAttacks) of
    Just aid -> Left (AttackEndpointUndeclared aid)
    Nothing -> Right ()
  validateGroups (envLeafIds env) groups
  elaboratedRev <- foldM (elabOne env) [] argDecls
  -- Attack paths resolve last: a 'StepName' is resolved against the rule at its
  -- position in the *elaborated* target argument, which does not exist until
  -- every argument is lowered.
  attacks <- mapM (resolveSurfaceAttack pol (reverse elaboratedRev)) surfaceAttacks
  queries <- mapM (resolveStatus claims) statusIds
  pure
    ( Unit
        { unitRules = map stripPremiseLabels (policyRules pol)
        , unitContraries = policyContraries pol
        , unitExceptions = policyExceptions pol
        , unitTheories = registryTheories reg
        , unitLeaves = gamma
        , unitArgs = reverse elaboratedRev
        , unitAttacks = attacks
        , unitQueries = queries
        , unitGroups = groups
        , unitGroupMode = policyGroupMode pol
        }
    , generated
    )

-- | Drop a rule's presentation-only premise labels on the way into 'Unit'.
--
-- Grammar App. B.4 states the invariant directly: \"labels never enter @Unit@\"
-- — @cmp@ and @0@ resolve to the same 'StepPremise' and the rule's compiled
-- form is unchanged. 'unitRules' is otherwise a verbatim copy of
-- 'policyRules', so this is the one place the invariant can be enforced.
-- (Byte-identity does not depend on it: "Lara.Wire".@encodeRule@ names its
-- eight encoded fields explicitly and labels are not among them. This keeps the
-- /value/ honest as well as the bytes.)
stripPremiseLabels :: Rule -> Rule
stripPremiseLabels r = r {rulePremiseLabels = []}

-- | Lower an authored attack to the frozen 'Attack' (grammar §7 AMENDMENT,
-- App. B.5).
--
-- An integer segment is a 'StepPremise' directly, unchanged from
-- @lara-syntax\@0.2@. A 'StepName' is resolved __against the targeted rule__ to
-- either a premise label (App. B.4) or a critical-question id — at most one of
-- the two, guaranteed by 'validatePremiseLabels'. Both spellings therefore
-- lower to the same 'Position', which is why the compiled AF is byte-identical
-- whichever the author wrote.
resolveSurfaceAttack
  :: Policy
  -> [(ArgId, SupportTerm)]
  -> SurfaceAttack
  -> Either ElabError Attack
resolveSurfaceAttack pol args k = case k of
  SRebut w u -> Right (Rebut w u)
  SUndercut w u steps -> Undercut w u <$> resolvePath pol args w u steps
  SUndermine w u steps -> Undermine w u <$> resolvePath pol args w u steps

-- | Resolve one position path against the elaborated target argument.
--
-- The walk descends the target's support term so that a /deeper/ segment
-- resolves against the rule occurrence it actually names, not against the root.
-- When no rule is in hand — the occurrence is a leaf, its rule is undeclared, or
-- the path runs past the term — the remaining segments keep their
-- @lara-syntax\@0.2@ reading (integer ⇒ premise, name ⇒ question) and no error
-- is raised: those paths are @checkAttack@'s to reject as R10\/R11, and
-- preserving the old reading is what keeps every existing example's 'Unit'
-- unchanged.
resolvePath
  :: Policy
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> ArgId
  -> [SurfaceStep]
  -> Either ElabError [Step]
resolvePath pol args source target = go (lookup target args)
  where
    go _ [] = Right []
    go mterm (s : rest) = case mterm >>= occurrence of
      Nothing -> Right (map legacyStep (s : rest))
      Just (rule, prems, disch) -> do
        (step, next) <- resolveStep rule prems disch s
        (step :) <$> go next rest

    -- The rule occurrence at the current position, with its sub-terms.
    occurrence (SRule rid _ prems disch _ _) =
      (\r -> (r, prems, disch)) <$> find ((== rid) . ruleId) (policyRules pol)
    occurrence (SLeaf _) = Nothing

    resolveStep rule prems disch s = case s of
      StepIndex i -> Right (StepPremise i, prems `at` i)
      StepName n
        | Just i <- premiseLabelIndex rule n -> Right (StepPremise i, prems `at` i)
        | Just q <- questionNamed rule n -> Right (StepQuestion q, lookup q disch)
        | otherwise -> Left (AttackStepUnresolved source target n)

    legacyStep (StepIndex i) = StepPremise i
    legacyStep (StepName n) = StepQuestion (QuestionId n)

    xs `at` i
      | i >= 0, i < length xs = Just (xs !! i)
      | otherwise = Nothing

-- | The __0-based__ premise slot a rule's premise label names (App. B.4, eng
-- review 6A). 'rulePremiseLabels' is positionally aligned with 'rulePremises',
-- and is @[]@ when no premise is labelled.
premiseLabelIndex :: Rule -> String -> Maybe Int
premiseLabelIndex rule n =
  lookup (PremiseLabel n) (zip [l | Just l <- rulePremiseLabels rule] indices)
  where
    indices = [i | (i, Just _) <- zip [0 ..] (rulePremiseLabels rule)]

-- | The rule's critical question of that name, if it declares one.
questionNamed :: Rule -> String -> Maybe QuestionId
questionNamed rule n =
  find (== QuestionId n) (map questionId (ruleQuestions rule))

-- | Premise-label well-formedness for one policy (grammar App. B.4): labels are
-- unique within a rule, disjoint from that rule's question ids, and may not
-- spell §7's terminal markers @rule@\/@leaf@ (otherwise @a2.leaf.leaf@ parses
-- two ways). Both namespaces are policy-declared, so a collision is statically
-- detectable and is rejected here, not discovered at an attack site.
validatePremiseLabels :: [Rule] -> Either ElabError ()
validatePremiseLabels = mapM_ one
  where
    one rule = do
      let labels = [l | Just l <- rulePremiseLabels rule]
          questions = [q | QuestionId q <- map questionId (ruleQuestions rule)]
          labelCount = length (rulePremiseLabels rule)
          premiseCount = length (rulePremises rule)
      when (labelCount /= 0 && labelCount /= premiseCount) $
        Left (PremiseLabelCountMismatch (ruleId rule) labelCount premiseCount)
      case firstDup labels of
        Just l -> Left (PremiseLabelDuplicate (ruleId rule) l)
        Nothing -> Right ()
      case find (\(PremiseLabel l) -> l `elem` attackPathTerminalMarkers) labels of
        Just l -> Left (PremiseLabelReserved (ruleId rule) l)
        Nothing -> Right ()
      case find (\(PremiseLabel l) -> l `elem` questions) labels of
        Just l -> Left (PremiseLabelQuestionCollision (ruleId rule) l)
        Nothing -> Right ()


-- | Raw argument endpoints of an authored attack, in source order. The @.lara@
-- front door validates these before constructing a 'Unit', matching the wire
-- decoder's R14 boundary and preserving raw/resolved attack alignment. Read off
-- the /surface/ attack because the check runs before path resolution, which
-- needs the elaborated arguments.
surfaceAttackEndpoints :: SurfaceAttack -> [ArgId]
surfaceAttackEndpoints attack = case attack of
  SRebut source target -> [source, target]
  SUndercut source target _ -> [source, target]
  SUndermine source target _ -> [source, target]

-- | Enforce duplicate-report-group well-formedness (R14) on the @.lara@ path,
-- mirroring "Lara.Wire".@checkGroupInvariants@ so both front doors reject the
-- same malformed group declarations. Without this a group naming an undeclared
-- leaf would reach 'Lara.Driver.groupConsistent', whose @lookup@ would silently
-- drop the dangling member and degenerate the group to a singleton — evading an
-- intended R9 rejection (the worst failure mode for a data-integrity feature).
-- The three checks — unique group ids, ≥2 distinct members, every member a
-- declared leaf — are exactly the wire decoder's, in the same order.
validateGroups :: [LeafId] -> [DupGroup] -> Either ElabError ()
validateGroups declared groups = do
  case firstDup [g | DupGroup g _ <- groups] of
    Just gid -> Left (DuplicateGroupId gid)
    Nothing -> Right ()
  mapM_ checkGroup groups
  where
    checkGroup (DupGroup gid members) = do
      case firstDup members of
        Just l -> Left (GroupRepeatedMember gid l)
        Nothing -> Right ()
      when (length members < 2) $ Left (GroupTooFewMembers gid)
      case find (`notElem` declared) members of
        Just l -> Left (GroupMemberUndeclared gid l)
        Nothing -> Right ()

-- | The first element that repeats (declaration order), matching the wire
-- decoder's @firstDup@.
firstDup :: Eq a => [a] -> Maybe a
firstDup = go []
  where
    go _ [] = Nothing
    go seen (x : rest)
      | x `elem` seen = Just x
      | otherwise = go (x : seen) rest

-- | Elaborate one argument, threading the prior arguments (accumulated in
-- reverse declaration order) so premise reconstruction can resolve to them.
elabOne
  :: Env
  -> [(ArgId, SupportTerm)]
  -> Arg
  -> Either ElabError [(ArgId, SupportTerm)]
elabOne env acc arg = do
  let aid = argId arg
      priors = reverse acc -- declaration order (lookup is order-insensitive)
  term <- elabTerm env priors aid (argTerm arg)
  validateConcl env aid (argConcl arg) term
  pure ((aid, term) : acc)

-- | Rebuild the full 'SupportTerm' from the shallow surface term.
elabTerm
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> SupportTerm
  -> Either ElabError SupportTerm
elabTerm env priors aid term = case term of
  -- A leaf stays a leaf; an undeclared id is left for checkUnit (R1).
  SLeaf l -> pure (SLeaf l)
  SRule r posTheta shallowPrems shallowDisch holes assurance -> do
    rule <-
      maybe (Left (UnknownRule aid r)) Right $
        find ((== r) . ruleId) (policyRules (envPolicy env))
    let params = ruleParams rule
        nGot = length posTheta
        nExp = length params
    when (nGot /= nExp) $ Left (ArityMismatch aid r nExp nGot)
    -- Re-associate positional θ with the rule's declared parameter names.
    let theta = zip params (map snd posTheta)
    prems <-
      if null shallowPrems
        then resolvePremises env priors aid r rule theta
        else mapM (elabTerm env priors aid) shallowPrems
    disch <- resolveDischarges env priors aid shallowDisch
    -- lara-syntax@0.2: lower assurance verbatim. Legality (strict mode,
    -- allow-trusted, certifier allowlist, replay) belongs to R7/R13.
    pure (SRule r theta prems disch holes assurance)

-- | Reconstruct each implicit premise by unique @≡@-match (spec §5). Preserves
-- premise order.
resolvePremises
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> RuleId
  -> Rule
  -> Subst
  -> Either ElabError [SupportTerm]
resolvePremises env priors aid r rule theta =
  mapM resolve (zip [1 ..] (rulePremises rule))
  where
    resolve :: (Int, AtomPat) -> Either ElabError SupportTerm
    resolve (i, apat) =
      let ground = apatToProp theta apat
          leafMatches =
            [ (l, SLeaf lid)
            | (lid@(LeafId l), p) <- envGamma env
            , equiv p ground
            ]
          argMatches =
            [ (a, t)
            | (ArgId a, t) <- priors
            , maybe False (equiv ground) (conclOf (envPolicy env) (envGamma env) t)
            ]
          matches = leafMatches ++ argMatches
       in case matches of
            [(_, t)] -> Right t
            [] -> Left (UnresolvedPremise aid r i ground)
            _ -> Left (AmbiguousPremise aid r i ground (map fst matches))

-- | Re-point each shallow discharge target: a declared leaf stays an 'SLeaf'; a
-- prior-argument id becomes that argument's elaborated term. (The answer-pattern
-- match is @checkUnit@'s R6 job; here we only build the sub-term.)
resolveDischarges
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> [(QuestionId, SupportTerm)]
  -> Either ElabError [(QuestionId, SupportTerm)]
resolveDischarges env priors aid = mapM one
  where
    one (q, SLeaf (LeafId ref))
      | LeafId ref `elem` envLeafIds env = Right (q, SLeaf (LeafId ref))
      | Just t <- lookup (ArgId ref) priors = Right (q, t)
      | otherwise = Left (UnresolvedDischarge aid q ref)
    -- The parser only ever produces 'SLeaf' discharge targets; a non-leaf
    -- sub-term is passed through unchanged (totality).
    one (q, t) = Right (q, t)

-- | Validate (and reclassify) the announced argument conclusion. The checker
-- consumes only the support term's own @concl(w)@, so this never changes the
-- 'Unit'; it is the trusted-elaborator check of the author's stated role
-- (grammar §6).
validateConcl :: Env -> ArgId -> ArgConcl -> SupportTerm -> Either ElabError ()
validateConcl env aid ac term = case ac of
  SupportsClaim c -> case find ((== c) . claimId) (envClaims env) of
    -- Declared claim: verify concl(w) ≡ its formal (spec §3.1).
    Just claim -> case conclOf (envPolicy env) (envGamma env) term of
      Just w
        | equiv w (claimFormal claim) -> Right ()
        | otherwise -> Left (ConclusionMismatch aid c w (claimFormal claim))
      -- Undeclared leaf root: concl unknown here; checkUnit rejects it (R1).
      Nothing -> Right ()
    -- Not a declared claim: treat as SupportsDerived (no error).
    Nothing -> Right ()
  SupportsDerived _ -> Right ()
  Challenges tgt -> case tgt of
    ChallengesQuestion _ u
      | u `elem` envArgIds env -> Right ()
      | otherwise -> Left (ChallengeTargetUndeclared aid)
    ChallengesLeaf l
      | l `elem` envLeafIds env -> Right ()
      | otherwise -> Left (ChallengeTargetUndeclared aid)

-- | Resolve a @status@ id to the declared claim's formal proposition.
resolveStatus :: [Claim] -> PropId -> Either ElabError Prop
resolveStatus claims pid = case find ((== pid) . claimId) claims of
  Just claim -> Right (claimFormal claim)
  Nothing -> Left (UnknownStatusClaim pid)

-- ---------------------------------------------------------------------------
-- Conclusion helper
-- ---------------------------------------------------------------------------

-- | @concl(w)@ (spec §6.1): a leaf's Γ proposition, or a rule instance's
-- conclusion pattern instantiated by θ. 'Nothing' when a leaf is undeclared or a
-- rule is unknown (both are downstream @checkUnit@ concerns).
conclOf :: Policy -> [(LeafId, Prop)] -> SupportTerm -> Maybe Prop
conclOf _ gamma (SLeaf l) = lookup l gamma
conclOf pol _ (SRule r theta _ _ _ _) = do
  rule <- find ((== r) . ruleId) (policyRules pol)
  Just (apatToProp theta (ruleConclusion rule))

-- ---------------------------------------------------------------------------
-- Pattern reclassification (grammar §2)
-- ---------------------------------------------------------------------------

-- | Reclassify every rule's (and exception's) pattern identifiers so that a bare
-- ident that is __not__ one of the enclosing rule's parameters becomes a ground
-- nullary constant, matching the encoding the checker consumes (a hand-built
-- rule writes a ground constant as @PCon k []@, only real parameters as 'PVar').
--
-- Rule premises\/conclusion\/question-answers scope over the rule's own
-- parameters. An exception atom scopes over its target rule's parameters (the θ
-- that @checkAttack@ instantiates it under; "Lara.Attack".@exceptionFailure@).
-- Contraries carry no parameter scope (their variables are universally
-- quantified, matched by "Lara.Attack".@matchPat@), so they pass through
-- unchanged.
reclassifyPolicy :: Policy -> Policy
reclassifyPolicy pol =
  pol
    { policyRules = map reclassifyRule (policyRules pol)
    , policyExceptions = map (reclassifyException (policyRules pol)) (policyExceptions pol)
    }

-- | Reclassify an exception atom against its target rule's parameters (the θ
-- @checkAttack@ instantiates it under). An exception naming an unknown rule
-- passes through unchanged.
reclassifyException :: [Rule] -> Exception -> Exception
reclassifyException rules ex =
  case find ((== exceptionRule ex) . ruleId) rules of
    Just r -> ex {exceptionAtom = reclassifyAPat (ruleParams r) (exceptionAtom ex)}
    Nothing -> ex

-- | Reclassify a rule's premise, conclusion, and question-answer patterns
-- against the rule's own parameters.
reclassifyRule :: Rule -> Rule
reclassifyRule r =
  r
    { rulePremises = map (reclassifyAPat ps) (rulePremises r)
    , ruleConclusion = reclassifyAPat ps (ruleConclusion r)
    , ruleQuestions =
        [q {questionAnswer = reclassifyAPat ps (questionAnswer q)} | q <- ruleQuestions r]
    }
  where
    ps = ruleParams r

-- | Reclassify an atom pattern's identifiers against a parameter set.
reclassifyAPat :: [Param] -> AtomPat -> AtomPat
reclassifyAPat params (AtomPat pr ps) = AtomPat pr (map (reclassifyPat params) ps)

-- | Reclassify a pattern: a 'PVar' outside @params@ is a ground nullary
-- constant; otherwise recurse structurally (grammar §2).
reclassifyPat :: [Param] -> Pat -> Pat
reclassifyPat params (PVar prm@(Param x))
  | prm `elem` params = PVar prm
  | otherwise = PCon (FunSym x) []
reclassifyPat params (PCon k ps) = PCon k (map (reclassifyPat params) ps)
reclassifyPat _ (PLit t) = PLit t
