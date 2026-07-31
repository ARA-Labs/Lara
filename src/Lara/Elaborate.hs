-- | The trusted surface elaborator: lower a presentation 'Program' (+ its
-- 'Policy') to the frozen checker anchor 'Unit' (spec plan A1b, D1/D3).
--
-- == Position in the pipeline
--
-- "Lara.Syntax" decodes @.lara@ text to the /presentation/ AST but records
-- support terms __shallowly__ (premises implicit, θ positional under synthetic
-- names @\"1\"..\"n\"@, discharges as bare 'SLeaf' refs; see the "Lara.Syntax"
-- header). This module rebuilds the __full__ 'SupportTerm' the checker consumes:
-- it re-associates θ with the rule's real parameter names, reconstructs each
-- implicit premise by unique @≡@-match against the declared leaves and prior
-- arguments (spec §5), and re-points discharge targets. The caller combines the
-- resulting 'Unit' with its source inputs via "Lara.Replay".'sourceCheckInput',
-- then passes that validated 'CheckInput' to "Lara.Driver".'runCheck'.
--
-- == Trusted, pure, deterministic, total on well-formed input
--
-- 'elaborate' is __inside the TCB__ (plan D1) and __pure__: it does __no IO, no
-- parsing, no filesystem access__. The caller (@app\/Main.hs@, Task A1c) does
-- file IO and co-located policy resolution and hands this function already-parsed
-- values. Keeping this boundary pure keeps M4b a two-way door: a machine producer
-- can build a 'Program' in memory and reuse this exact lowering (plan A1 "D1
-- ripple").
--
-- Premise resolution is a total function on well-formed input (plan D3): the
-- declared leaf+arg set is finite and @≡@ is decidable, so "the declared
-- conclusions @≡ Apᵢ·θ@" is computable — __exactly one__ ⇒ that sub-term,
-- __zero__ ⇒ 'UnresolvedPremise', __≥2__ ⇒ 'AmbiguousPremise'. No search, no
-- backtracking.
--
-- == Assurance
--
-- Strict /rules/ pass through into 'unitRules' as policy declarations.
-- Support-term assurance (lara-syntax@0.2, grammar App. A.1) is lowered
-- verbatim from the surface; the elaborator performs no mode or certifier
-- check — R7/R13 at @checkUnit@ are the single enforcement point.
module Lara.Elaborate
  ( -- * Caller-supplied environment inputs
    Sigma (..)
  , emptySigma
  , defeasibleSuiteSigma
  , TheoryRegistry (..)
  , emptyRegistry
  , registryOf
    -- * Elaboration errors (located-ish: they name the arg/rule/leaf/claim)
  , ElabError (..)
  , elabErrorMessage
    -- * The elaborator
  , elaborate
  ) where

import Control.Monad (foldM, when)
import Data.List (find)

import Lara.AST
import Lara.Prop (Prop (..), Term (..), equiv, prettyProp)

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
-- Elaboration errors
-- ---------------------------------------------------------------------------

-- | A located-ish elaboration failure. Each constructor names the offending
-- argument, rule, leaf, claim, or position so the caller can render a diagnostic
-- (see 'elabErrorMessage'). The elaborator is deterministic, so the /first/
-- error in declaration order is the one reported.
data ElabError
  = -- | @programPolicy prog@ ≠ @policyId policy@ (the header-match invariant).
    PolicyIdMismatch PolicyId PolicyId
  | -- | a @by r(…)@ names a rule absent from the policy: @arg@, @rule@.
    UnknownRule ArgId RuleId
  | -- | positional θ length ≠ the rule's parameter count: @arg@, @rule@,
    -- expected, got.
    ArityMismatch ArgId RuleId Int Int
  | -- | no declared leaf\/prior-arg conclusion @≡@ the ground premise: @arg@,
    -- @rule@, 1-based premise index, the ground premise proposition.
    UnresolvedPremise ArgId RuleId Int Prop
  | -- | ≥2 declared conclusions @≡@ the ground premise: @arg@, @rule@, premise
    -- index, the ground premise, and the matching leaf\/arg ids.
    AmbiguousPremise ArgId RuleId Int Prop [String]
  | -- | a @discharge q with ref@ whose @ref@ is neither a declared leaf nor a
    -- prior arg: @arg@, @question@, the ref name.
    UnresolvedDischarge ArgId QuestionId String
  | -- | a @supports(c)@ over a declared claim whose term conclusion ≠ the claim
    -- formal: @arg@, @claim@, @concl(w)@, @claimFormal(c)@.
    ConclusionMismatch ArgId PropId Prop Prop
  | -- | a @status c@ whose @c@ is not a declared claim.
    UnknownStatusClaim PropId
  | -- | a @challenges(…)@ whose target arg\/leaf is not declared (diagnostic
    -- only; never affects the 'Unit').
    ChallengeTargetUndeclared ArgId
  | -- | two @group@ declarations share an id (R14 well-formedness): the id.
    DuplicateGroupId GroupId
  | -- | a @group@ repeats a member (R14 well-formedness): @group@, the member.
    GroupRepeatedMember GroupId LeafId
  | -- | a @group@ has fewer than two members, so it cannot report a conflict
    -- (R14 well-formedness): the group id.
    GroupTooFewMembers GroupId
  | -- | a @group@ member is not a declared leaf (R14 well-formedness): @group@,
    -- the undeclared member.
    GroupMemberUndeclared GroupId LeafId
  deriving (Eq, Show)

-- | Render an 'ElabError' as a single human-readable line.
elabErrorMessage :: ElabError -> String
elabErrorMessage e = case e of
  PolicyIdMismatch (PolicyId p) (PolicyId q) ->
    "program declares policy '" ++ p ++ "' but the supplied policy is '" ++ q ++ "'"
  UnknownRule (ArgId a) (RuleId r) ->
    "arg '" ++ a ++ "': unknown rule '" ++ r ++ "' (not declared in the policy)"
  ArityMismatch (ArgId a) (RuleId r) expd got ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' expects " ++ show expd
      ++ " argument(s) but " ++ show got ++ " were supplied"
  UnresolvedPremise (ArgId a) (RuleId r) i g ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' premise #" ++ show i
      ++ " (" ++ prettyProp g ++ ") matches no declared leaf or prior argument"
  AmbiguousPremise (ArgId a) (RuleId r) i g ms ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' premise #" ++ show i
      ++ " (" ++ prettyProp g ++ ") is ambiguous — matched " ++ show ms
  UnresolvedDischarge (ArgId a) (QuestionId q) ref ->
    "arg '" ++ a ++ "': discharge of '" ++ q ++ "' names '" ++ ref
      ++ "', which is neither a declared leaf nor a prior argument"
  ConclusionMismatch (ArgId a) (PropId c) w formal ->
    "arg '" ++ a ++ "': supports(" ++ c ++ ") but its conclusion "
      ++ prettyProp w ++ " ≢ the claim formal " ++ prettyProp formal
  UnknownStatusClaim (PropId c) ->
    "status '" ++ c ++ "': not a declared claim"
  ChallengeTargetUndeclared (ArgId a) ->
    "arg '" ++ a ++ "': challenges(…) target is not a declared argument or leaf"
  DuplicateGroupId (GroupId g) ->
    "group '" ++ g ++ "': duplicate group id"
  GroupRepeatedMember (GroupId g) (LeafId l) ->
    "group '" ++ g ++ "': repeats member '" ++ l ++ "'"
  GroupTooFewMembers (GroupId g) ->
    "group '" ++ g ++ "': fewer than two members (cannot report a conflict)"
  GroupMemberUndeclared (GroupId g) (LeafId l) ->
    "group '" ++ g ++ "': member '" ++ l ++ "' is not a declared leaf"

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
-- Field-by-field (plan A1b):
--
--   * @unitRules\/unitContraries\/unitExceptions@ pass through from the policy
--     (@checkUnit@ validates policy well-formedness incl. R12);
--   * @unitTheories@ from the registry (empty for the defeasible suite);
--   * @unitLeaves@ (Γ) = every declared leaf — __admission default is all-admit__
--     (outside-voice #12); an undeclared leaf reference is left for @checkUnit@ to
--     reject as R1 (kept distinct from the outside-the-core R8 admission class);
--   * @unitArgs@ in declaration order (order fixes AF node indices, hence labels);
--     each shallow support term is rebuilt to the full 'SupportTerm';
--   * @unitAttacks@ pass through (the surface already lowered positions);
--   * @unitQueries@ = the @status@-named claims' formals;
--   * @unitGroups@ = the declared duplicate-report groups (spec §4.3), with
--     @unitGroupMode@ baked from the policy's conflict escalation choice.
elaborate :: Sigma -> TheoryRegistry -> Program -> Policy -> Either ElabError Unit
elaborate _sigma reg prog pol0 = do
  when (programPolicy prog /= policyId pol0) $
    Left (PolicyIdMismatch (programPolicy prog) (policyId pol0))
  -- Reclassify pattern identifiers (grammar §2): the shallow parser records
  -- every bare pattern ident as a 'PVar', but a non-parameter ident is a ground
  -- constant. The checker's premise instantiation ('instAPat') treats an unbound
  -- 'PVar' as failure (R3), so this resolution is mandatory elaborator work.
  let pol = reclassifyPolicy pol0
      decls = programDecls prog
      gamma = [(leafId l, leafProp l) | DeclLeaf l <- decls]
      claims = [c | DeclClaim c <- decls]
      argDecls = [a | DeclArg a <- decls]
      attacks = [k | DeclAttack k <- decls]
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
  validateGroups (envLeafIds env) groups
  elaboratedRev <- foldM (elabOne env) [] argDecls
  queries <- mapM (resolveStatus claims) statusIds
  pure
    Unit
      { unitRules = policyRules pol
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
  SRule r posTheta _shallowPrems shallowDisch holes assurance -> do
    rule <-
      maybe (Left (UnknownRule aid r)) Right $
        find ((== r) . ruleId) (policyRules (envPolicy env))
    let params = ruleParams rule
        nGot = length posTheta
        nExp = length params
    when (nGot /= nExp) $ Left (ArityMismatch aid r nExp nGot)
    -- Re-associate positional θ with the rule's declared parameter names.
    let theta = zip params (map snd posTheta)
    prems <- resolvePremises env priors aid r rule theta
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
-- Conclusion / substitution helpers
-- ---------------------------------------------------------------------------

-- | @concl(w)@ (spec §6.1): a leaf's Γ proposition, or a rule instance's
-- conclusion pattern instantiated by θ. 'Nothing' when a leaf is undeclared or a
-- rule is unknown (both are downstream @checkUnit@ concerns).
conclOf :: Policy -> [(LeafId, Prop)] -> SupportTerm -> Maybe Prop
conclOf _ gamma (SLeaf l) = lookup l gamma
conclOf pol _ (SRule r theta _ _ _ _) = do
  rule <- find ((== r) . ruleId) (policyRules pol)
  Just (apatToProp theta (ruleConclusion rule))

-- | Instantiate an atom pattern to a ground proposition under θ.
apatToProp :: Subst -> AtomPat -> Prop
apatToProp theta (AtomPat p ps) = Prop p (map (patToTerm theta) ps)

-- | Instantiate a pattern to a ground term under θ, reclassifying a bare
-- identifier the parser recorded as a 'PVar': it is a parameter iff it is in θ's
-- domain (= the rule's declared parameters), otherwise a ground constant
-- (grammar §2).
patToTerm :: Subst -> Pat -> Term
patToTerm theta (PVar prm@(Param x)) = case lookup prm theta of
  Just t -> t
  Nothing -> TCon (FunSym x) []
patToTerm _ (PLit t) = t
patToTerm theta (PCon k ps) = TCon k (map (patToTerm theta) ps)

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
