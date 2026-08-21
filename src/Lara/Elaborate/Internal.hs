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
-- == The four sibling modules
--
-- The elaborator is split so the @lara-syntax\@0.5@ consuming surface pass and
-- structural lowering can share a failure vocabulary:
--
--   * "Lara.Elaborate.Error" — 'ElabError' and its renderer (re-exported here);
--   * "Lara.Elaborate.Subst" — pattern instantiation and one-way matching;
--   * "Lara.Elaborate.ValueBinding" — the consuming @let@ substitution and
--     @nl@ interpolation pass; and
--   * "Lara.Elaborate.Comparison" — the later @comparison@ expansion.
module Lara.Elaborate.Internal
  ( -- * Caller-supplied environment inputs
    TheoryRegistry (..)
  , emptyRegistry
  , registryOf
    -- * Elaboration errors (located-ish: they name the arg/rule/leaf/claim)
    --
    -- | Defined in "Lara.Elaborate.Error" and re-exported here, so that module,
    -- "Lara.Elaborate.ValueBinding", and "Lara.Elaborate.Comparison" can raise
    -- the same failures without an import cycle; existing importers are unaffected.
  , ElabError (..)
  , elabErrorMessage
    -- * The elaborator (admission-free; see the module header)
  , elaborate
  , elaborateWithProvenance
  , elaborateWithSemanticProgram
  , GeneratedArg (..)
  ) where

import Control.Monad (foldM, when)
import Data.List (find)

import Lara.AST
import Lara.Elaborate.CertSlots (SlotRefError (..), lowerCertPayload)
import Lara.Elaborate.Comparison (GeneratedArg (..), expandSurfaceProvenance)
import Lara.Elaborate.Error (ElabError (..), elabErrorMessage)
import Lara.Elaborate.Subst
  ( MatchFailure (..)
  , apatToProp
  , matchAPat
  )
import Lara.Syntax (attackPathTerminalMarkers)
import Lara.Prop (Prop, equiv)

-- ---------------------------------------------------------------------------
-- Caller-supplied environment inputs
-- ---------------------------------------------------------------------------

-- The proposition signature @Σ@ is __no longer a caller-supplied input__
-- (@lara-core\@0.2@, #89). It is declared by the policy ('policySigma') and
-- copied verbatim into 'unitSigma' below, so there is exactly one place it can
-- come from and no caller can hand the elaborator a signature the policy does
-- not declare. The object itself lives in "Lara.Sigma".

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

-- | A reference selected by inferred theta, keeping its exact semantic term
-- paired with the proposition used for matching.
data ResolvedArgRef = ResolvedArgRef
  { resolvedRefTerm :: SupportTerm
  , resolvedRefProp :: Prop
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
-- @lara-syntax\@0.4@ inserts the consuming value-binding pass first. The
-- @lara-syntax\@0.3@ comparison stage then expands every @comparison@ block to
-- the declarations it stands for ('Lara.Elaborate.Comparison.expandSurface').
-- Those two presentation passes run before id checks, argument lowering, or
-- attack-path resolution. The @lara-syntax\@0.5 theta inference step runs
-- per-argument inside the lowering fold, after those passes and before the
-- corresponding conclusion and later attack validation.
elaborate :: TheoryRegistry -> Program -> Policy -> Either ElabError Unit
elaborate reg prog pol = projectUnit <$> elaborateWithSemanticProgram reg prog pol
  where
    projectUnit (unit, _, _) = unit

-- | 'elaborate' paired with comparison-generation provenance. This public
-- projection preserves the pre-0.4 result shape.
elaborateWithProvenance
  :: TheoryRegistry
  -> Program
  -> Policy
  -> Either ElabError (Unit, [GeneratedArg])
elaborateWithProvenance reg prog pol =
  project <$> elaborateWithSemanticProgram reg prog pol
  where
    project (unit, generated, _) = (unit, generated)

-- | Package-internal complete elaboration result. The 'Program' is the exact
-- post-binding, post-comparison semantic presentation used to construct the
-- returned 'Unit'; secondary consumers must use it rather than re-expanding.
elaborateWithSemanticProgram
  :: TheoryRegistry
  -> Program
  -> Policy
  -> Either ElabError (Unit, [GeneratedArg], Program)
elaborateWithSemanticProgram reg prog0 pol0 = do
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
        { unitSigma = policySigma pol
        , unitRules = map stripPremiseLabels (policyRules pol)
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
    , prog
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
  term <- elabInstantiation env priors aid (argInstantiation arg)
  validateConcl env aid (argConcl arg) term
  pure ((aid, term) : acc)

-- | Lower the complete presentation support payload to a semantic term.
elabInstantiation
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> ArgInstantiation
  -> Either ElabError SupportTerm
elabInstantiation env priors aid inst = case inst of
  ExplicitTheta term -> elabTerm env priors aid term
  InferTheta r refs shallowDisch holes assurance -> do
    rule <- lookupRule env aid r
    (theta, prems) <- inferTheta env priors aid rule refs
    disch <- resolveArgDischarges env priors aid shallowDisch
    -- lara-syntax@0.6 (#105): named certificate premise slots lower here,
    -- after premise resolution, because a slot is an index into @prems@.
    assurance' <- lowerArgCert env priors aid prems assurance
    pure (SRule r theta prems disch holes assurance')

lookupRule :: Env -> ArgId -> RuleId -> Either ElabError Rule
lookupRule env aid r =
  maybe (Left (UnknownRule aid r)) Right $
    find ((== r) . ruleId) (policyRules (envPolicy env))

-- | Rebuild the full 'SupportTerm' for an explicit presentation payload.
elabTerm
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> SupportTerm
  -> Either ElabError SupportTerm
elabTerm env priors aid term = case term of
  SLeaf l -> pure (SLeaf l)
  SRule r posTheta shallowPrems shallowDisch holes assurance -> do
    rule <- lookupRule env aid r
    (theta, prems) <- do
      let params = ruleParams rule
          nGot = length posTheta
          nExp = length params
      when (nGot /= nExp) $ Left (ArityMismatch aid r nExp nGot)
      -- Re-associate positional θ with the rule's declared parameter names.
      let theta' = zip params (map snd posTheta)
      prems' <-
        if null shallowPrems
          then resolvePremises env priors aid r rule theta'
          else mapM (elabTerm env priors aid) shallowPrems
      pure (theta', prems')
    disch <- resolveDischarges env priors aid shallowDisch
    -- lara-syntax@0.2: lower assurance verbatim. Legality (strict mode,
    -- allow-trusted, certifier allowlist, replay) belongs to R7/R13.
    -- lara-syntax@0.6 (#105) adds exactly one rewrite above that: symbolic
    -- premise references become the numeric slots the backend already decodes.
    -- 'elabTerm' recurses, so a nested instance's certificate lowers against
    -- its own premise list, not the enclosing one (D8).
    assurance' <- lowerArgCert env priors aid prems assurance
    pure (SRule r theta prems disch holes assurance')

-- | The one namespace lookup shared by every argument-body source reference:
-- the @lara-syntax\@0.5@ θ references ('resolveArgRef'), the @\@0.6@
-- certificate premise-slot references ('certSlotResolver', #105), and the
-- @\@0.7@ discharge targets ('resolveDischargeRef', #129). It answers which
-- declared leaves and which prior arguments carry this source name, matched on
-- the bare source name, in declaration order.
--
-- All three callers now share one collision policy on top of that lookup: a
-- name carried by both a declared leaf and a prior argument is ambiguous and
-- is rejected, never silently resolved to either. #129 closed the last
-- carve-out (discharge targets used to prefer the leaf); grammar Appendix F.4
-- records the unified rule. Callers still keep their own error /family/, since
-- each names a different surface position.
refMatches
  :: Env
  -> [(ArgId, SupportTerm)]
  -> String
  -> ([(LeafId, Prop)], [(ArgId, SupportTerm)])
refMatches env priors name =
  ( [ (leafId, prop)
    | (leafId@(LeafId leafName), prop) <- envGamma env
    , leafName == name
    ]
  , [ (argId, term)
    | (argId@(ArgId argName), term) <- priors
    , argName == name
    ]
  )

-- | Resolve one symbolic certificate premise reference (#105) to the 0-based
-- slot it occupies in @prems@, the citing instance's __already resolved__
-- premise list.
--
-- The name scope is 'refMatches' — exactly the one a θ reference sees — and
-- the collision policy is the same: a name that is both a declared leaf and a
-- prior argument is ambiguous, never silently one of them. What differs is the
-- second step, which a θ reference does not have: the resolved source must
-- also /be a premise of this instance/, at exactly one slot.
--
-- Locating is by term equality against the premise list, because that is what
-- premise resolution stores: a leaf premise is @'SLeaf' l@ ('resolvePremises',
-- 'resolveArgRef'), and a prior-argument premise is that argument's own
-- elaborated term. An authored premise list — which the @\@0.6@ surface
-- grammar cannot yet write, but 'elabTerm' accepts — spells a prior argument
-- the way the parser spells every identifier, as @'SLeaf' ('LeafId' a)@, so
-- both representations count as a hit for the prior-argument case. Otherwise a
-- citation would lower under @from […]@ and then fail with a spurious
-- 'CertSlotNotAPremise' once the same instance is written out.
certSlotResolver
  :: Env
  -> [(ArgId, SupportTerm)]
  -> [SupportTerm] -- ^ this instance's resolved premises, in slot order
  -> String
  -> Either SlotRefError Int
certSlotResolver env priors prems name =
  case refMatches env priors name of
    ([(leafId, _)], []) -> locate [SLeaf leafId]
    ([], [(_, term)]) -> locate [term, SLeaf (LeafId name)]
    ([], []) -> Left SlotNameUnresolved
    _ -> Left SlotNameAmbiguous
  where
    locate candidates =
      case [i | (i, p) <- zip [0 ..] prems, p `elem` candidates] of
        [i] -> Right i
        [] -> Left SlotNameNotAPremise
        (i : j : _) -> Left (SlotNameMultiSlot i j)

-- | Lower the symbolic premise references of one rule instance's assurance
-- (#105), against that instance's own resolved premises. Every other assurance
-- passes through: only 'AssuranceCert' has a payload, and even then only a
-- backend with a declared 'Lara.Strict.Cell.SlotSchema' is touched.
--
-- This is where the pass's failures become author-facing: the resolver's
-- 'SlotRefError' vocabulary is backend-shaped, so it is translated here into
-- the located 'ElabError' family, attributed to the enclosing @arg@ (the unit
-- an author reads and edits) and naming the backend as @beta\@version@.
lowerArgCert
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> [SupportTerm]
  -> Assurance
  -> Either ElabError Assurance
lowerArgCert env priors aid prems assurance = case assurance of
  AssuranceCert cert ->
    case lowerCertPayload (certSlotResolver env priors prems) cert of
      Right cert' -> Right (AssuranceCert cert')
      Left (name, err) -> Left (certSlotError aid cert name err)
  _ -> Right assurance

-- | Translate one resolver\/lowering verdict into its located 'ElabError'.
certSlotError :: ArgId -> Cert -> String -> SlotRefError -> ElabError
certSlotError aid cert name err = case err of
  SlotNameUnresolved -> CertSlotUnresolved aid backend version ref
  SlotNameAmbiguous -> CertSlotAmbiguous aid backend version ref
  SlotNameNotAPremise -> CertSlotNotAPremise aid backend version ref
  SlotNameMultiSlot i j -> CertSlotMultiSlot aid backend version ref i j
  SlotNonCanonicalNumeral -> CertSlotNonCanonicalNumeral aid backend version ref
  SlotSchemaMismatch -> CertSlotSchemaMismatch aid backend version ref
  where
    backend = certBackend cert
    version = certVersion cert
    ref = ArgRef name

-- | Resolve one inferred reference in leaf/prior-argument scope order.
resolveArgRef
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> RuleId
  -> Int
  -> ArgRef
  -> Either ElabError ResolvedArgRef
resolveArgRef env priors aid rid i ref@(ArgRef name) =
  case refMatches env priors name of
    ([(leafId, prop)], []) ->
      Right (ResolvedArgRef (SLeaf leafId) prop)
    ([], [(_, term)]) ->
      case conclOf (envPolicy env) (envGamma env) term of
        Just prop -> Right (ResolvedArgRef term prop)
        Nothing -> Left (ThetaReferenceConclUnderivable aid rid i ref)
    ([], []) -> Left (ThetaReferenceUnresolved aid rid i ref)
    _ -> Left (ThetaReferenceAmbiguous aid rid i ref)

-- | Derive an inferred rule theta and retain the references' selected terms.
inferTheta
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> Rule
  -> [ArgRef]
  -> Either ElabError (Subst, [SupportTerm])
inferTheta env priors aid rule refs = do
  let expected = length (rulePremises rule)
      got = length refs
      rid = ruleId rule
  when (got /= expected) $
    Left (ThetaReferenceCountMismatch aid rid expected got)
  resolved <- mapM (uncurry (resolveArgRef env priors aid rid)) (zip [1 ..] refs)
  theta0 <- foldM matchOne [] $
    zip3 [1 :: Int ..] refs (zip (rulePremises rule) resolved)
  mapM_ (requireThetaParameter aid rid theta0) (ruleParams rule)
  let theta =
        [ (param, term)
        | param <- ruleParams rule
        , Just term <- [lookup param theta0]
        ]
  pure (theta, map resolvedRefTerm resolved)
  where
    matchOne sub (i, ref, (apat, resolved)) =
      case matchAPat sub apat (resolvedRefProp resolved) of
        Right next -> Right next
        Left MatchShape ->
          Left
            ( ThetaReferenceShapeMismatch
                aid
                (ruleId rule)
                i
                ref
                (resolvedRefProp resolved)
            )
        Left (MatchConflict param old new) ->
          Left
            ( ThetaReferenceConflict
                aid
                (ruleId rule)
                i
                ref
                param
                old
                new
            )

    requireThetaParameter arg ruleId' theta0 param
      | param `elem` map fst theta0 = Right ()
      | otherwise = Left (ThetaParameterUnbound arg ruleId' param)

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
    one (q, SLeaf (LeafId ref)) = do
      target <- resolveDischargeRef env priors aid q ref
      pure (q, target)
    -- The parser only ever produces 'SLeaf' discharge targets; a non-leaf
    -- sub-term is passed through unchanged (totality).
    one (q, t) = Right (q, t)

-- | Resolve the identifier-only discharge map carried by an inferred payload.
resolveArgDischarges
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> ArgDischarge
  -> Either ElabError [(QuestionId, SupportTerm)]
resolveArgDischarges env priors aid = mapM one
  where
    one (q, ArgRef ref) = do
      target <- resolveDischargeRef env priors aid q ref
      pure (q, target)

-- | Resolve one @discharge q with ref@ target, for both payload forms: the
-- explicit one ('resolveDischarges', where the parser spells the target
-- @'SLeaf' ('LeafId' ref)@) and the inferred one ('resolveArgDischarges',
-- where it arrives as @'ArgRef' ref@). One function so the two surfaces cannot
-- drift apart.
--
-- The name scope and the collision policy both come from 'refMatches' — the
-- same ones a θ reference ('resolveArgRef') and a certificate premise slot
-- ('certSlotResolver') see. Before #129 this position silently preferred the
-- declared leaf when a name carried both; it is now an 'AmbiguousDischarge'.
-- "Prior" is whatever 'elabOne' has accumulated, i.e. strictly earlier in
-- declaration order, so a discharge naming a /later/ argument is unresolved,
-- not a forward reference.
resolveDischargeRef
  :: Env
  -> [(ArgId, SupportTerm)]
  -> ArgId
  -> QuestionId
  -> String
  -> Either ElabError SupportTerm
resolveDischargeRef env priors aid q ref =
  case refMatches env priors ref of
    ([(leafId, _)], []) -> Right (SLeaf leafId)
    ([], [(_, term)]) -> Right term
    ([], []) -> Left (UnresolvedDischarge aid q (ArgRef ref))
    _ -> Left (AmbiguousDischarge aid q (ArgRef ref))

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
