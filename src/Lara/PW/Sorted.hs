-- | Sorted queries, symbol translation, the decidable rule clause, and the
-- tagged cross-world comparison: the Haskell mirror of
-- @lean\/Lara\/PW\/Sorted.lean@, @Translation.lean@, @Compare.lean@ and the
-- @ruleOkB@ decider of @Surface.lean@.
--
-- Every function here is a transcription of a Lean definition that the
-- differential gate (@scripts\/check-pw-conformance.py@) compares on shared
-- fixtures. The Lean side carries the theorems: 'queryFault' is exactly
-- well-sortedness, 'vocabFault' is exactly 'trAtom'\'s domain, and a comparison
-- profile is exactly the model's @⟨b⟩@ reading.
module Lara.PW.Sorted
  ( -- * Symbol maps and translation (Lean @Lara.PW.Translation@)
    SymMap (..)
  , symMapOf
  , trTerm
  , trAtom
  , trRule
    -- * The one decidable clause of T6 (Lean @ruleOkB@)
  , ruleOk
    -- * Posing (Lean @Sorted.queryFault@)
  , QueryFault (..)
  , queryFault
  , OutOfVocabulary (..)
  , vocabFault
  , PosingFault (..)
    -- * Tagged comparison (Lean @crossCompare@ \/ @crossComparePosed@)
  , IncomparabilityReason (..)
  , CrossResult (..)
  , SortedResult (..)
  , crossCompare
  , crossComparePosed
  ) where

import Lara.AST
  ( AtomPat (..)
  , Pat (..)
  , Question (..)
  , Rule (..)
  , Status
  )
import Lara.Policy (lookupRule)
import Lara.Prop (FunSym, Pred, Prop (..), Term (..))
import Lara.PW.Surface (SymEntry (..))
import Lara.Sigma (Sigma, SortFault (..), sortCheckProp)

-- ---------------------------------------------------------------------------
-- Symbol maps
-- ---------------------------------------------------------------------------

-- | A partial symbol translation (Lean @SymMap@).
data SymMap = SymMap
  { predMap :: Pred -> Maybe Pred
  , conMap :: FunSym -> Maybe FunSym
  }

-- | The map a declared entry list denotes: first match wins, undefined
-- outside the declaration (Lean @symMapOf@).
symMapOf :: [SymEntry] -> SymMap
symMapOf entries =
  SymMap
    { predMap = \p -> lookup p [(s, t) | SymPred s t <- entries]
    , conMap = \k -> lookup k [(s, t) | SymCon s t <- entries]
    }

-- | Literals unchanged, constructors through 'conMap' (Lean @trTerm@).
trTerm :: SymMap -> Term -> Maybe Term
trTerm m t = case t of
  TNum s -> Just (TNum s)
  TStr s -> Just (TStr s)
  TCon k ts -> TCon <$> conMap m k <*> mapM (trTerm m) ts

-- | The claim translation (Lean @trAtom@).
trAtom :: SymMap -> Prop -> Maybe Prop
trAtom m (Prop p ts) = Prop <$> predMap m p <*> mapM (trTerm m) ts

trPat :: SymMap -> Pat -> Maybe Pat
trPat m p = case p of
  PVar x -> Just (PVar x)
  PLit t -> Just (PLit t)
  PCon k ps -> PCon <$> conMap m k <*> mapM (trPat m) ps

trAtomPat :: SymMap -> AtomPat -> Maybe AtomPat
trAtomPat m (AtomPat p ps) = AtomPat <$> predMap m p <*> mapM (trPat m) ps

trQuestion :: SymMap -> Question -> Maybe Question
trQuestion m q = (\a -> q {questionAnswer = a}) <$> trAtomPat m (questionAnswer q)

-- | Premises, conclusion and question answers translate; every other field is
-- carried unchanged (Lean @trRule@).
trRule :: SymMap -> Rule -> Maybe Rule
trRule m r = do
  premises <- mapM (trAtomPat m) (rulePremises r)
  conclusion <- trAtomPat m (ruleConclusion r)
  questions <- mapM (trQuestion m) (ruleQuestions r)
  pure r {rulePremises = premises, ruleConclusion = conclusion, ruleQuestions = questions}

-- | Every rule the source policy resolves translates, and the target policy
-- carries the translation at the same identifier (Lean @ruleOkB@, which
-- @ruleOkB_iff@ proves is T6's @rule_ok@ clause).
ruleOk :: SymMap -> [Rule] -> [Rule] -> Bool
ruleOk m source target = all ok (map ruleId source)
  where
    ok rn = case lookupRule source rn of
      Nothing -> True
      Just r -> case trRule m r of
        Nothing -> False
        Just r' -> lookupRule target rn == Just r'

-- ---------------------------------------------------------------------------
-- Posing
-- ---------------------------------------------------------------------------

-- | Why an atom is not a query of a signature (Lean @QueryFault@).
data QueryFault
  = UndeclaredPredicate Pred
  | IllSortedArguments Pred
  deriving (Eq, Show)

-- | 'Nothing' exactly on a well-sorted atom; otherwise the head predicate,
-- undeclared or wrongly applied (Lean @queryFault@). The checker's own
-- 'sortCheckProp' decides well-sortedness, so posing and R2 cannot disagree.
queryFault :: Sigma -> Prop -> Maybe QueryFault
queryFault sg a@(Prop p _) = case sortCheckProp sg a of
  Nothing -> Nothing
  Just (FaultUndeclaredPred _) -> Just (UndeclaredPredicate p)
  Just _ -> Just (IllSortedArguments p)

-- | A symbol a bridge's map does not carry (Lean @OutOfVocabulary@).
data OutOfVocabulary
  = OovPred Pred
  | OovCon FunSym
  deriving (Eq, Show)

-- | The first symbol 'trAtom' cannot carry, in its own traversal order (Lean
-- @vocabFault@).
vocabFault :: SymMap -> Prop -> Maybe OutOfVocabulary
vocabFault m (Prop p ts) = case predMap m p of
  Nothing -> Just (OovPred p)
  Just _ -> vocabFaultTerms ts
  where
    vocabFaultTerms = foldr (\t rest -> maybe rest Just (vocabFaultTerm t)) Nothing
    vocabFaultTerm t = case t of
      TCon k args -> case conMap m k of
        Nothing -> Just (OovCon k)
        Just _ -> vocabFaultTerms args
      _ -> Nothing

-- | Why a claim cannot be posed as a comparison query (Lean @PosingFault@).
data PosingFault
  = SourceQuery QueryFault
  | BridgeVocabulary OutOfVocabulary
  | TargetQuery QueryFault
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Comparison
-- ---------------------------------------------------------------------------

-- | Why a comparison produced no profile (Lean @IncomparabilityReason@).
data IncomparabilityReason
  = TranslationUndefined
  | NoCandidateWorld
  | AllCandidateBridgesRejected
  deriving (Eq, Show)

-- | A nonempty profile or a reason (Lean @CrossResult@).
data CrossResult a
  = Incomparable IncomparabilityReason
  | Comparable a [a]
  deriving (Eq, Show)

-- | A posing fault or a comparison result (Lean @SortedResult@).
data SortedResult
  = NotPosable PosingFault
  | Compared (CrossResult Status)
  deriving (Eq, Show)

-- | Translation, then candidates, then acceptance (Lean @crossCompare@).
crossCompare :: Maybe q -> [w] -> (w -> Bool) -> (w -> q -> Status) -> CrossResult Status
crossCompare t candidates acceptB statusOf = case t of
  Nothing -> Incomparable TranslationUndefined
  Just d
    | null candidates -> Incomparable NoCandidateWorld
    | otherwise -> case filter acceptB candidates of
        [] -> Incomparable AllCandidateBridgesRejected
        v : vs -> Comparable (statusOf v d) (map (`statusOf` d) vs)

-- | Pose at the source, translate to a target query, then compare (Lean
-- @crossComparePosed@). No world is consulted for a posing fault.
crossComparePosed
  :: Sigma
  -> Sigma
  -> SymMap
  -> Prop
  -> [w]
  -> (w -> Bool)
  -> (w -> Prop -> Status)
  -> SortedResult
crossComparePosed sgS sgT m raw candidates acceptB statusOf =
  case queryFault sgS raw of
    Just f -> NotPosable (SourceQuery f)
    Nothing -> case trAtom m raw of
      -- Lean reaches @translationUndefined@ here only when 'vocabFault' has no
      -- symbol to report, which @vocabFault_isSome_of_trAtom_none@ excludes;
      -- the arm is kept so the transcription is total and literal.
      Nothing -> case vocabFault m raw of
        Just f -> NotPosable (BridgeVocabulary f)
        Nothing -> Compared (Incomparable TranslationUndefined)
      Just a -> case queryFault sgT a of
        Just f -> NotPosable (TargetQuery f)
        Nothing -> Compared (crossCompare (Just a) candidates acceptB statusOf)
