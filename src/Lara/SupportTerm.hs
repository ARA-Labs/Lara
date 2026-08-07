-- | Executable support-term checking (spec §6.1) — the Haskell mirror of the
-- executable checker in @lean/Lara/Check/Support.lean@ plus the @leaves@ helper
-- of @lean/Lara/Support.lean@.
--
-- This is the decision procedure @inferSupport@ (Lean @inferSupport@ /
-- @inferSupportRaw@): a total structural recursion over a 'SupportTerm' that
-- either rejects with a located, symbolic 'CheckError' or returns the term's
-- unique conclusion and obligation set ('SupportResult', Lean @SupportResult@).
-- The relational judgment @HasSupport@ and its soundness\/completeness proofs
-- live in the Lean development; here we port only the executable half — the
-- oracle the Haskell production runtime runs (plan D14: the mirror is the audit
-- backbone).
--
-- The certificate seam is the abstract 'CertOk' oracle (Lean @certOkOf@ /
-- @certOkBOf@ over a backend-first registry): the executable checker never
-- inspects a certificate payload, it only asks the oracle. "Lara.Check" and the
-- @lara@ driver build the oracle from the wire @theories@ over the one
-- implemented backend, @nd\@1@.
module Lara.SupportTerm
  ( -- * The support-check result
    SupportResult (..)
    -- * Retained checked node (Lean @Compile.CheckedNode@)
    -- | Opaque: the constructor is hidden so a \"checked\" node cannot be forged;
    -- see "Lara.SupportTerm.Internal". Read via 'cnTerm' \/ 'cnConclusion'.
  , CheckedNode
  , cnTerm
  , cnConclusion
    -- * The certificate oracle (Lean @certOkOf@)
  , CertOk
  , CertOutcome (..)
  , certAccepted
    -- * Located, symbolic diagnostics (Lean @Lara.Check.Error@)
  , CheckLoc (..)
  , ReferenceReason (..)
  , SubstitutionReason (..)
  , PremiseReason (..)
  , QuestionReason (..)
  , DischargeReason (..)
  , AssuranceReason (..)
  , BackendReason (..)
  , AttackKind (..)
  , AttackOccurrenceKind (..)
  , AttackPositionReason (..)
  , AttackRelationReason (..)
  , CheckError (..)
  , checkErrorClass
    -- * Instantiation (spec §4.1)
  , instPat
  , instPats
  , instAPat
  , instAPats
    -- * Obligation accounting (spec §6.1)
  , questionNames
  , mandatoryNames
  , dedupQuestions
  , openMandatory
  , collectObligations
  , holeNames
    -- * Leaf dependency report (spec §6)
  , leaves
    -- * Side-condition deciders
  , substDomainB
  , atomsEquivB
  , strictNoQuestionB
  , assuranceOkB
  , certAllowed
    -- * The executable checker
  , inferSupport
  ) where

import Lara.AST
import Lara.Prop (Prop (..), Term (..), equiv)
import Lara.SupportTerm.Internal (CheckedNode (..))

-- ---------------------------------------------------------------------------
-- Result and node types
-- ---------------------------------------------------------------------------

-- | The unique conclusion and obligation set of a checked term (Lean
-- @Support.SupportResult@).
data SupportResult = SupportResult
  { srConclusion :: Prop
  , srObligations :: [QuestionId]
  }
  deriving (Eq, Show)

-- | The outcome of the certificate oracle: accepted, or rejected /with the
-- backend's own reason/.
--
-- The oracle is 'Bool'-valued in the mechanization (Lean @certOkBOf@), and the
-- checked graph still depends on nothing more than 'certAccepted' — every
-- acceptance decision, and therefore every soundness statement, ranges over
-- that projection alone. The reason rides alongside for one purpose: reaching
-- the author. Before this, the one rejection class produced by a /registered/
-- backend was also the only one that said nothing — bare @reject R13@ with
-- empty @stderr@ — in a checker whose selling point is located rejections.
data CertOutcome
  = CertAccepted
  | -- | The reason the backend adapter returned.
    CertRejected String
  deriving (Eq, Show)

-- | The acceptance projection: the /only/ part of 'CertOutcome' the checked
-- graph may consult, and exactly the old @Bool@ oracle.
certAccepted :: CertOutcome -> Bool
certAccepted CertAccepted = True
certAccepted (CertRejected _) = False

-- | The executable certificate-acceptance oracle (mirrors Lean @certOkBOf@ over
-- a @BackendRegistry@): given the assurance's opaque certificate, the
-- instantiated premise atoms @As@, and the conclusion @C@, decide replay. The
-- checker never inspects the payload — it only calls this oracle (the factivity
-- firewall). "Lara.Check.checkUnit" receives it as an input.
--
-- A 'CertOk' is a /pure function/, and that — not a call count — is what makes
-- the reason trustworthy. 'assuranceOkB' branches on 'certAccepted'; on the
-- error path 'assuranceError' applies the same oracle to the same @(cert, As,
-- C)@ to recover the reason, so the two applications are the same value and a
-- diagnostic cannot disagree with the decision it explains. That is why this is
-- not a second evaluation /path/: there is one function, @Bool@ is its
-- projection, and the diagnostic reads the other projection of the same result.
-- (The cost is confined to the rejecting branch: an accepted step asks once.)
type CertOk = Cert -> [Prop] -> Prop -> CertOutcome

-- ---------------------------------------------------------------------------
-- Located, symbolic diagnostics (Lean @lean/Lara/Check/Error.lean@)
-- ---------------------------------------------------------------------------

-- | A location inside a support term (Lean @CheckLoc@): the root, a numbered
-- premise, or a named critical-question discharge, nested.
data CheckLoc
  = LocRoot
  | LocPremise CheckLoc Int
  | LocQuestion CheckLoc QuestionId
  deriving (Eq, Show)

-- | R1 reference failures (Lean @ReferenceReason@).
data ReferenceReason
  = MissingLeaf LeafId
  | MissingRule RuleId
  | UndeclaredAttackSource SupportTerm
  | UndeclaredAttackTarget SupportTerm
  deriving (Eq, Show)

-- | R3 substitution failures (Lean @SubstitutionReason@).
data SubstitutionReason
  = DuplicateKeys [Param]
  | DomainMismatch [Param] [Param]
  | PremiseInstantiation [AtomPat]
  | ConclusionInstantiation AtomPat
  deriving (Eq, Show)

-- | R4 premise failures (Lean @PremiseReason@).
data PremiseReason
  = PremiseCount Int Int
  | PremiseMismatch Prop Prop
  deriving (Eq, Show)

-- | R5 question-accounting failures (Lean @QuestionReason@).
data QuestionReason
  = DuplicateDeclarations [QuestionId]
  | DuplicateDischarges [QuestionId]
  | DuplicateHoles [QuestionId]
  | Uncovered [QuestionId] [QuestionId] [QuestionId]
  | Overlap [QuestionId] [QuestionId]
  | UndeclaredDischarge [QuestionId] [QuestionId]
  | UndeclaredHole [QuestionId] [QuestionId]
  deriving (Eq, Show)

-- | R6 discharge/answer failures (Lean @DischargeReason@).
data DischargeReason
  = AnswerInstantiation QuestionId AtomPat
  | ConclusionMismatch QuestionId Prop Prop
  deriving (Eq, Show)

-- | R7 assurance failures (Lean @AssuranceReason@).
data AssuranceReason
  = QuestionsPresent [QuestionId] [QuestionId]
  | WrongMode Mode Assurance
  | TrustedDisallowed
  | CertifierUnallowlisted BackendId TheoryDigest
  deriving (Eq, Show)

-- | R13 backend failures (Lean @BackendReason@).
--
-- 'ReplayRejected' carries the backend adapter's own reason string. It is a
-- diagnostic payload only: 'Lara.Diagnostics.rejectionOf' maps every
-- constructor here to the same wire class @R13@, so the string never reaches
-- @stdout@ and the wire verdict is unchanged. The Lean @BackendReason@
-- deliberately has no such field — see "Lara.Driver.Internal" for why the two
-- drivers are allowed to differ here.
data BackendReason
  = BackendMissing BackendId
  | DigestMissing BackendId TheoryDigest
  | ReplayRejected BackendId TheoryDigest CertRef String
  deriving (Eq, Show)

-- | The attack kinds, for R10\/R11 diagnostics (Lean @AttackKind@).
data AttackKind = AKRebut | AKUndercut | AKUndermine
  deriving (Eq, Show)

-- | Which occurrence kind an attack expected (Lean @AttackOccurrenceKind@).
data AttackOccurrenceKind = OccRule | OccLeaf
  deriving (Eq, Show)

-- | R10 positional failures (Lean @AttackPositionReason@).
data AttackPositionReason
  = UndefinedPosition
  | WrongOccurrenceKind AttackOccurrenceKind AttackOccurrenceKind
  deriving (Eq, Show)

-- | R11 attack-relation failures (Lean @AttackRelationReason@).
data AttackRelationReason
  = MissingTargetRule RuleId
  | TargetConclusionInstantiation RuleId AtomPat
  | MissingTargetLeaf LeafId
  | StrictTarget RuleId
  | MissingContrary Prop Prop
  | MissingException RuleId
  | ExceptionInstantiation RuleId AtomPat
  | ExceptionMismatch RuleId Prop Prop
  deriving (Eq, Show)

-- | The frozen located checker rejections (Lean @CheckError@). Named distinctly
-- from 'Lara.AST.RejectClass' so both can be imported unqualified.
data CheckError
  = CE_R1 CheckLoc ReferenceReason
  | CE_R3 CheckLoc SubstitutionReason
  | CE_R4 CheckLoc PremiseReason
  | CE_R5 CheckLoc QuestionReason
  | CE_R6 CheckLoc DischargeReason
  | CE_R7 CheckLoc AssuranceReason
  | CE_R10 CheckLoc Position AttackKind AttackPositionReason
  | CE_R11 CheckLoc Position AttackKind AttackRelationReason
  | CE_R13 CheckLoc BackendReason
  deriving (Eq, Show)

-- | The frozen rejection class of a located error (Lean @CheckError.rejectClass@).
checkErrorClass :: CheckError -> RejectClass
checkErrorClass e = case e of
  CE_R1{} -> R1
  CE_R3{} -> R3
  CE_R4{} -> R4
  CE_R5{} -> R5
  CE_R6{} -> R6
  CE_R7{} -> R7
  CE_R10{} -> R10
  CE_R11{} -> R11
  CE_R13{} -> R13

-- ---------------------------------------------------------------------------
-- Instantiation (spec §4.1; Lean @instPat@ family)
-- ---------------------------------------------------------------------------

-- | Instantiate a pattern under a ground substitution (Lean @instPat@); @Nothing@
-- iff a variable is unbound. A literal pattern instantiates to its own term
-- ('PLit' folds Lean's @.num@\/@.str@ cases).
instPat :: Subst -> Pat -> Maybe Term
instPat theta p = case p of
  PVar x -> lookup x theta
  PLit t -> Just t
  PCon k ps -> TCon k <$> instPats theta ps

-- | Instantiate a pattern list pointwise (Lean @instPats@).
instPats :: Subst -> [Pat] -> Maybe [Term]
instPats theta = mapM (instPat theta)

-- | Instantiate an atom pattern to a ground atom (Lean @instAPat@).
instAPat :: Subst -> AtomPat -> Maybe Prop
instAPat theta (AtomPat pr ps) = Prop pr <$> instPats theta ps

-- | Instantiate a premise-pattern list (Lean @instAPats@).
instAPats :: Subst -> [AtomPat] -> Maybe [Prop]
instAPats theta = mapM (instAPat theta)

-- ---------------------------------------------------------------------------
-- Obligation accounting (spec §6.1; Lean @collectObligations@ family)
-- ---------------------------------------------------------------------------

-- | The rule's declared question names (Lean @questionNames@).
questionNames :: Rule -> [QuestionId]
questionNames r = map questionId (ruleQuestions r)

-- | The rule's mandatory question names (Lean @mandatoryNames@).
mandatoryNames :: Rule -> [QuestionId]
mandatoryNames r =
  [questionId q | q <- ruleQuestions r, questionNecessity q == Mandatory]

-- | Deterministically remove repeated question identifiers, keeping the first
-- occurrence's position under a right-fold (Lean @dedupQuestions@ semantics:
-- membership preserved, result 'Nodup').
dedupQuestions :: [QuestionId] -> [QuestionId]
dedupQuestions [] = []
dedupQuestions (q : qs) =
  let rest = dedupQuestions qs
   in if q `elem` rest then rest else q : rest

-- | The hole set of an instance as question names. The AST types a hole as an
-- 'ObligationId' — the spec §2 obligation name class @o@, kept as its own
-- newtype so the surface syntax can name obligations separately from questions
-- (the symbolic-core discipline: distinct namespaces get distinct types). The
-- §6.1 accounting, however, treats a hole as the /question name/ it leaves open
-- (Lean @H : List QuestionId@; the Lean driver decodes @holes@ straight to
-- 'QuestionId', collapsing the two). The names share their textual identity, so
-- this one sanctioned cast is the deliberate spec-obligation → executable-question
-- bridge, confined to exactly this boundary.
holeNames :: [ObligationId] -> [QuestionId]
holeNames = map (\(ObligationId s) -> QuestionId s)

-- | @H ∩ mandatory(r)@: the obligations an instance's hole set contributes
-- (Lean @openMandatory@).
openMandatory :: Rule -> [QuestionId] -> [QuestionId]
openMandatory r hs = [n | n <- hs, n `elem` mandatoryNames r]

-- | The exact obligation set of an instance: child-premise, child-discharge,
-- and open-mandatory obligations unioned as sets (Lean @collectObligations@).
collectObligations
  :: [[QuestionId]] -> [[QuestionId]] -> Rule -> [QuestionId] -> [QuestionId]
collectObligations premOs dischOs r hs =
  dedupQuestions (concat (premOs ++ dischOs ++ [openMandatory r hs]))

-- ---------------------------------------------------------------------------
-- Leaf dependency report (spec §6; Lean @leaves@)
-- ---------------------------------------------------------------------------

-- | The leaf constants occurring in a term, discharge subterms included (Lean
-- @leaves@ — the reported dependency set /is/ this list, spec §6).
leaves :: SupportTerm -> [LeafId]
leaves t = case t of
  SLeaf l -> [l]
  SRule _ _ ws d _ _ ->
    concatMap leaves ws ++ concatMap (leaves . snd) d

-- ---------------------------------------------------------------------------
-- Side-condition deciders (Lean @substDomainB@ / @atomsEquivB@ / …)
-- ---------------------------------------------------------------------------

-- | @dom(theta) = params@ exactly (Lean @substDomainB@).
substDomainB :: Subst -> Rule -> Bool
substDomainB theta r =
  all (`elem` ps) keys && all (`elem` keys) ps
  where
    keys = map fst theta
    ps = ruleParams r

-- | Pointwise @≡@ on two atom lists of equal length (Lean @atomsEquivB@).
atomsEquivB :: [Prop] -> [Prop] -> Bool
atomsEquivB [] [] = True
atomsEquivB (a : as) (b : bs) = equiv a b && atomsEquivB as bs
atomsEquivB _ _ = False

-- | A strict instance carries no discharge map and no holes (Lean
-- @strictNoQuestionB@).
strictNoQuestionB :: Rule -> [(QuestionId, SupportTerm)] -> [QuestionId] -> Bool
strictNoQuestionB r d hs =
  ruleMode r /= Strict || (null d && null hs)

-- | Does a rule allow the certificate's @(backend\@version, theory)@ pair?
-- (Lean's @(β, h) ∈ r.certifiers@).
certAllowed :: Rule -> BackendId -> Int -> TheoryDigest -> Bool
certAllowed r b v h =
  any
    (\cr -> certRefBackend cr == b && certRefVersion cr == v && certRefTheory cr == h)
    (ruleCertifiers r)

-- | The @assurance(m, alpha)@ side condition (Lean @assuranceOkB@).
assuranceOkB :: CertOk -> Rule -> [Prop] -> Prop -> Assurance -> Bool
assuranceOkB certOk r as c a = case a of
  AssuranceNone -> ruleMode r == Defeasible
  AssuranceTrusted -> ruleMode r == Strict && ruleAllowTrusted r
  AssuranceCert cert@(Cert b v h _) ->
    ruleMode r == Strict && certAllowed r b v h && certAccepted (certOk cert as c)

-- | Does a discharge conclusion answer its question's pattern? (Lean
-- @answerOkB@). Unknown discharge keys are skipped here (Lean @knownAnswersOkB@):
-- the later accounting pass reports them as R5.
answerOkB :: Subst -> [Question] -> QuestionId -> Prop -> Bool
answerOkB theta questions q a =
  any
    ( \qd ->
        questionId qd == q
          && case instAPat theta (questionAnswer qd) of
            Nothing -> False
            Just aq -> equiv a aq
    )
    questions

knownAnswersOkB
  :: Subst -> [Question] -> [(QuestionId, SupportTerm)] -> [SupportResult] -> Bool
knownAnswersOkB _ _ [] [] = True
knownAnswersOkB theta questions ((q, _) : d) (res : results) =
  ( if q `elem` map questionId questions
      then answerOkB theta questions q (srConclusion res)
      else True
  )
    && knownAnswersOkB theta questions d results
knownAnswersOkB _ _ _ _ = False

-- ---------------------------------------------------------------------------
-- Error constructors (Lean @premiseError@ / @answerError@ / @assuranceError@)
-- ---------------------------------------------------------------------------

firstPremiseMismatch :: Int -> [Prop] -> [Prop] -> Maybe (Int, Prop, Prop)
firstPremiseMismatch _ [] [] = Nothing
firstPremiseMismatch i (a : as) (b : bs)
  | equiv a b = firstPremiseMismatch (i + 1) as bs
  | otherwise = Just (i, b, a)
firstPremiseMismatch _ _ _ = Nothing

premiseError :: CheckLoc -> [Prop] -> [Prop] -> CheckError
premiseError loc expected actual =
  case firstPremiseMismatch 0 actual expected of
    Just (i, ex, ac) -> CE_R4 (LocPremise loc i) (PremiseMismatch ex ac)
    Nothing -> CE_R4 loc (PremiseCount (length expected) (length actual))

firstBadAnswer
  :: Subst
  -> [Question]
  -> [(QuestionId, SupportTerm)]
  -> [SupportResult]
  -> Maybe (QuestionId, DischargeReason)
firstBadAnswer _ _ [] [] = Nothing
firstBadAnswer theta questions ((q, _) : d) (res : results) =
  case [qd | qd <- questions, questionId qd == q] of
    [] -> firstBadAnswer theta questions d results
    (qd : _) -> case instAPat theta (questionAnswer qd) of
      Nothing -> Just (q, AnswerInstantiation q (questionAnswer qd))
      Just aq ->
        if equiv (srConclusion res) aq
          then firstBadAnswer theta questions d results
          else Just (q, ConclusionMismatch q aq (srConclusion res))
firstBadAnswer _ _ _ _ = Nothing

answerError
  :: Subst
  -> [Question]
  -> [(QuestionId, SupportTerm)]
  -> [SupportResult]
  -> CheckLoc
  -> AtomPat
  -> CheckError
answerError theta questions d results loc fallback =
  case firstBadAnswer theta questions d results of
    Just (q, reason) -> CE_R6 (LocQuestion loc q) reason
    Nothing ->
      CE_R6
        loc
        (AnswerInstantiation (headDefault (QuestionId "") (map fst d)) fallback)

assuranceError :: CertOk -> Rule -> [Prop] -> Prop -> Assurance -> CheckLoc -> CheckError
assuranceError certOk r as c a loc = case a of
  AssuranceNone -> CE_R7 loc (WrongMode (ruleMode r) a)
  AssuranceTrusted ->
    if ruleMode r == Strict
      then CE_R7 loc TrustedDisallowed
      else CE_R7 loc (WrongMode (ruleMode r) a)
  AssuranceCert cert@(Cert b v h _) ->
    if ruleMode r /= Strict
      then CE_R7 loc (WrongMode (ruleMode r) a)
      else
        if not (certAllowed r b v h)
          then CE_R7 loc (CertifierUnallowlisted b h)
          -- The checker reaches this branch only when the oracle already
          -- rejected a certifier-allowed certificate, i.e. a replay rejection.
          -- Re-asking the oracle on the identical arguments recovers the reason
          -- it gave: 'CertOk' is a pure function and this is the same
          -- application, so the reason cannot describe a different decision
          -- than the one that sent us here — this is a second /application/,
          -- never a second evaluation path. 'CertAccepted' is unreachable;
          -- if it ever occurred, the honest thing is to say nothing rather than
          -- invent a cause, so it maps to the empty reason.
          else CE_R13 loc (ReplayRejected b h (CertRef b v h) (reasonOf (certOk cert as c)))
  where
    reasonOf CertAccepted = ""
    reasonOf (CertRejected msg) = msg

-- ---------------------------------------------------------------------------
-- The executable checker (Lean @inferSupportRaw@ mutual block)
-- ---------------------------------------------------------------------------

require :: Bool -> CheckError -> Either CheckError ()
require ok err = if ok then Right () else Left err

-- | Infer a support term's conclusion and obligations, or reject with a located
-- error (Lean @inferSupport@ \/ @inferSupportRaw@). @Pi@ is the rule lookup,
-- @Gamma@ the leaf context, @certOk@ the certificate oracle.
inferSupport
  :: (RuleId -> Maybe Rule)
  -> (LeafId -> Maybe Prop)
  -> CertOk
  -> CheckLoc
  -> SupportTerm
  -> Either CheckError SupportResult
inferSupport pI gamma certOk = go
  where
    go loc w = case w of
      SLeaf l -> case gamma l of
        Nothing -> Left (CE_R1 loc (MissingLeaf l))
        Just c -> Right (SupportResult c [])
      SRule rn theta ws d hs a -> do
        r <- case pI rn of
          Nothing -> Left (CE_R1 loc (MissingRule rn))
          Just r -> Right r
        require
          (nodup (map fst theta))
          (CE_R3 loc (DuplicateKeys (map fst theta)))
        require
          (substDomainB theta r)
          (CE_R3 loc (DomainMismatch (map fst theta) (ruleParams r)))
        as <- case instAPats theta (rulePremises r) of
          Nothing -> Left (CE_R3 loc (PremiseInstantiation (rulePremises r)))
          Just as -> Right as
        c <- case instAPat theta (ruleConclusion r) of
          Nothing -> Left (CE_R3 loc (ConclusionInstantiation (ruleConclusion r)))
          Just c -> Right c
        premiseResults <- goPremises loc 0 ws
        dischargeResults <- goDischarges loc d
        require
          (length premiseResults == length as)
          (CE_R4 loc (PremiseCount (length as) (length premiseResults)))
        require
          (atomsEquivB (map srConclusion premiseResults) as)
          (premiseError loc as (map srConclusion premiseResults))
        require
          (knownAnswersOkB theta (ruleQuestions r) d dischargeResults)
          (answerError theta (ruleQuestions r) d dischargeResults loc (ruleConclusion r))
        let dkeys = map fst d
            qnames = questionNames r
            hns = holeNames hs
        require (nodup qnames) (CE_R5 loc (DuplicateDeclarations qnames))
        require (nodup dkeys) (CE_R5 loc (DuplicateDischarges dkeys))
        require (nodup hns) (CE_R5 loc (DuplicateHoles hns))
        require
          (all (\qd -> questionId qd `elem` dkeys || questionId qd `elem` hns) (ruleQuestions r))
          (CE_R5 loc (Uncovered qnames dkeys hns))
        require
          (all (`notElem` hns) dkeys)
          (CE_R5 loc (Overlap dkeys hns))
        require
          (all (`elem` qnames) dkeys)
          (CE_R5 loc (UndeclaredDischarge dkeys qnames))
        require
          (all (`elem` qnames) hns)
          (CE_R5 loc (UndeclaredHole hns qnames))
        require
          (strictNoQuestionB r d hns)
          (CE_R7 loc (QuestionsPresent dkeys hns))
        require
          (assuranceOkB certOk r as c a)
          (assuranceError certOk r as c a loc)
        pure
          ( SupportResult
              c
              ( collectObligations
                  (map srObligations premiseResults)
                  (map srObligations dischargeResults)
                  r
                  hns
              )
          )

    goPremises _ _ [] = Right []
    goPremises loc i (w : ws) = do
      res <- go (LocPremise loc i) w
      rest <- goPremises loc (i + 1) ws
      pure (res : rest)

    goDischarges _ [] = Right []
    goDischarges loc ((q, w) : d) = do
      res <- go (LocQuestion loc q) w
      rest <- goDischarges loc d
      pure (res : rest)

-- ---------------------------------------------------------------------------
-- Local list helpers
-- ---------------------------------------------------------------------------

nodup :: Eq a => [a] -> Bool
nodup = go []
  where
    go _ [] = True
    go seen (x : xs) = x `notElem` seen && go (x : seen) xs

headDefault :: a -> [a] -> a
headDefault d = foldr (\x _ -> x) d
