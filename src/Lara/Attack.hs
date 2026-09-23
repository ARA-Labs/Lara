-- | Executable positional attack checking (spec §7.1) — the Haskell mirror of
-- @lean/Lara/Check/Attack.lean@ (the executable @checkAttack@ decision
-- procedure) plus the exact contrary matcher of @lean/Lara/Attack.lean@
-- (@contraryMatchB@ / @matchAPat@).
--
-- The wire 'Lara.AST.Attack' addresses its endpoints by 'ArgId'; the checker
-- works on the /resolved/ form 'RAttack' whose endpoints are the support terms
-- those ids name (mirroring the Lean @Lara.Attack.Attack@, whose endpoints are
-- terms — the driver resolves ids at the decode boundary). 'checkAttack' infers
-- the source's conclusion and then runs the occurrence-local target check
-- ('checkAttackTarget'): the three attack kinds are exactly the three position
-- kinds (root conclusion, internal rule occurrence, frontier leaf).
module Lara.Attack
  ( -- * Resolved attacks (Lean @Lara.Attack.Attack@)
    RAttack (..)
  , rSource
  , rTarget
    -- * Defeat-relevant policy content (Lean @DefeatPolicy@)
  , DefeatPolicy (..)
    -- * Positions
  , lookupDis
  , subterm
    -- * Exact contrary matching (Lean @contraryMatchB@)
  , matchPat
  , matchPats
  , matchAPat
  , contraryMatchDecl
  , contraryMatchB
    -- * The executable attack checker
  , checkAttackTarget
  , checkAttack
  ) where

import Lara.AST
import Lara.Prop (Prop (..), Term (..), equiv, nfTerm)
import Lara.SupportTerm

-- ---------------------------------------------------------------------------
-- Resolved attacks
-- ---------------------------------------------------------------------------

-- | A positional attack with endpoints resolved to support terms (Lean
-- @Lara.Attack.Attack@). 'Lara.AST.Attack' is the id-based wire form.
data RAttack
  = RRebut SupportTerm SupportTerm
  | RUndercut SupportTerm SupportTerm Position
  | RUndermine SupportTerm SupportTerm Position
  deriving (Eq, Show)

-- | The attacking argument @w@ (Lean @Attack.source@).
rSource :: RAttack -> SupportTerm
rSource k = case k of
  RRebut w _ -> w
  RUndercut w _ _ -> w
  RUndermine w _ _ -> w

-- | The attacked declared argument @u@ (Lean @Attack.target@).
rTarget :: RAttack -> SupportTerm
rTarget k = case k of
  RRebut _ u -> u
  RUndercut _ u _ -> u
  RUndermine _ u _ -> u

-- ---------------------------------------------------------------------------
-- Defeat-relevant policy content (Lean @DefeatPolicy@)
-- ---------------------------------------------------------------------------

-- | The @contrary@\/@exception@ declarations the attack checker consults (Lean
-- @DefeatPolicy@). Built from the unit's 'Lara.AST.Contrary' and
-- 'Lara.AST.Exception' lists.
data DefeatPolicy = DefeatPolicy
  { dpContraries :: [Contrary]
  , dpExceptions :: [Exception]
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Positions (spec §7; Lean @subterm@ / @lookupDis@)
-- ---------------------------------------------------------------------------

-- | First-match lookup of a discharge subterm by question id (Lean @lookupDis@).
lookupDis :: [(QuestionId, SupportTerm)] -> QuestionId -> Maybe SupportTerm
lookupDis [] _ = Nothing
lookupDis ((q', w) : rest) q
  | q' == q = Just w
  | otherwise = lookupDis rest q

-- | @u\@π@: the subterm occurrence at position @π@, partial (Lean @subterm@).
subterm :: SupportTerm -> Position -> Maybe SupportTerm
subterm u [] = Just u
subterm (SLeaf _) (_ : _) = Nothing
subterm (SRule _ _ ws _ _ _) (StepPremise i : pos) =
  case indexMaybe ws i of
    Just w -> subterm w pos
    Nothing -> Nothing
subterm (SRule _ _ _ d _ _) (StepQuestion q : pos) =
  case lookupDis d q of
    Just w -> subterm w pos
    Nothing -> Nothing

indexMaybe :: [a] -> Int -> Maybe a
indexMaybe xs i
  | i < 0 = Nothing
  | otherwise = case drop i xs of
      (x : _) -> Just x
      [] -> Nothing

-- ---------------------------------------------------------------------------
-- Exact contrary matching (Lean @contraryMatchB@ / @matchAPat@)
-- ---------------------------------------------------------------------------

-- | Match a pattern against a ground term, threading a substitution (Lean
-- @matchPat@). @canon@ is applied only at equality boundaries; here the fixed
-- 'nfTerm' plays that role. 'PLit' folds Lean's @.num@\/@.str@ cases: a literal
-- pattern matches a term iff their normal forms agree.
matchPat :: Subst -> Pat -> Term -> Maybe Subst
matchPat rho p t = case p of
  PVar x -> case lookup x rho of
    Nothing -> Just ((x, t) : rho)
    Just u -> if nfTerm u == nfTerm t then Just rho else Nothing
  PLit lit -> if nfTerm lit == nfTerm t then Just rho else Nothing
  PCon k ps -> case t of
    TCon k' ts -> if k == k' then matchPats rho ps ts else Nothing
    _ -> Nothing

-- | Match a pattern list against a term list (Lean @matchPats@).
matchPats :: Subst -> [Pat] -> [Term] -> Maybe Subst
matchPats rho [] [] = Just rho
matchPats rho (p : ps) (t : ts) = case matchPat rho p t of
  Nothing -> Nothing
  Just rho' -> matchPats rho' ps ts
matchPats _ _ _ = Nothing

-- | Match an atom pattern against a ground atom (Lean @matchAPat@).
matchAPat :: Subst -> AtomPat -> Prop -> Maybe Subst
matchAPat rho (AtomPat pr args) (Prop pr' ts)
  | pr == pr' = matchPats rho args ts
  | otherwise = Nothing

-- | Does a single declared @contrary A B@ match @(p, q)@? (Lean
-- @contraryMatchDecl@): match @A@ against @p@, then @B@ against @q@ under the
-- accumulated substitution.
contraryMatchDecl :: Prop -> Prop -> Contrary -> Bool
contraryMatchDecl p q (Contrary a b) =
  case matchAPat [] a p of
    Nothing -> False
    Just rho -> case matchAPat rho b q of
      Nothing -> False
      Just _ -> True

-- | Some declared contrary pair matches @(p, q)@ (Lean @contraryMatchB@).
contraryMatchB :: [Contrary] -> Prop -> Prop -> Bool
contraryMatchB contraries p q = any (contraryMatchDecl p q) contraries

-- ---------------------------------------------------------------------------
-- The executable attack checker (Lean @checkAttackTarget@ / @checkAttack@)
-- ---------------------------------------------------------------------------

-- | The undercut exception scan (Lean @exceptionFailure@): find a declared
-- exception for the target rule whose instantiated pattern is @≡@ the source
-- conclusion; retain the first informative failure reason otherwise.
exceptionFailure
  :: RuleId
  -> Subst
  -> Prop
  -> Position
  -> [Exception]
  -> Maybe AttackRelationReason
  -> Either CheckError ()
exceptionFailure rn _ _ pos [] prior =
  Left (CE_R11 LocRoot pos AKUndercut (maybe (MissingException rn) id prior))
exceptionFailure rn theta source pos (ex : rest) prior
  | exceptionRule ex == rn =
      case instAPat theta (exceptionAtom ex) of
        Nothing ->
          exceptionFailure rn theta source pos rest
            (orElse prior (ExceptionInstantiation rn (exceptionAtom ex)))
        Just ev ->
          if equiv source ev
            then Right ()
            else
              exceptionFailure rn theta source pos rest
                (orElse prior (ExceptionMismatch rn source ev))
  | otherwise = exceptionFailure rn theta source pos rest prior
  where
    orElse (Just r) _ = Just r
    orElse Nothing new = Just new

-- | The occurrence-local target check (Lean @checkAttackTarget@), given the
-- already-inferred source conclusion. The three attack kinds check the three
-- position kinds.
checkAttackTarget
  :: (RuleId -> Maybe Rule)
  -> (LeafId -> Maybe Prop)
  -> DefeatPolicy
  -> RAttack
  -> Prop
  -> Either CheckError ()
checkAttackTarget pI gamma dp k sc = case k of
  RRebut _ target -> case target of
    SLeaf _ ->
      Left (CE_R10 LocRoot [] AKRebut (WrongOccurrenceKind OccRule OccLeaf))
    SRule rn theta _ _ _ _ -> case pI rn of
      Nothing -> Left (CE_R11 LocRoot [] AKRebut (MissingTargetRule rn))
      Just r ->
        if ruleMode r == Defeasible
          then case instAPat theta (ruleConclusion r) of
            Nothing ->
              Left (CE_R11 LocRoot [] AKRebut (TargetConclusionInstantiation rn (ruleConclusion r)))
            Just tc ->
              if contraryMatchB (dpContraries dp) sc tc
                then Right ()
                else Left (CE_R11 LocRoot [] AKRebut (MissingContrary sc tc))
          else Left (CE_R11 LocRoot [] AKRebut (StrictTarget rn))
  RUndercut _ target pos -> case subterm target pos of
    Nothing -> Left (CE_R10 LocRoot pos AKUndercut UndefinedPosition)
    Just (SLeaf _) ->
      Left (CE_R10 LocRoot pos AKUndercut (WrongOccurrenceKind OccRule OccLeaf))
    Just (SRule rn theta _ _ _ _) -> case pI rn of
      Nothing -> Left (CE_R11 LocRoot pos AKUndercut (MissingTargetRule rn))
      Just r ->
        if ruleMode r == Defeasible
          then exceptionFailure rn theta sc pos (dpExceptions dp) Nothing
          else Left (CE_R11 LocRoot pos AKUndercut (StrictTarget rn))
  RUndermine _ target pos -> case subterm target pos of
    Nothing -> Left (CE_R10 LocRoot pos AKUndermine UndefinedPosition)
    Just (SRule{}) ->
      Left (CE_R10 LocRoot pos AKUndermine (WrongOccurrenceKind OccLeaf OccRule))
    Just (SLeaf l) -> case gamma l of
      Nothing -> Left (CE_R11 LocRoot pos AKUndermine (MissingTargetLeaf l))
      Just tc ->
        if contraryMatchB (dpContraries dp) sc tc
          then Right ()
          else Left (CE_R11 LocRoot pos AKUndermine (MissingContrary sc tc))

-- | Check one typed attack (Lean @checkAttack@): infer the source term's
-- conclusion, then run the target check.
checkAttack
  :: (RuleId -> Maybe Rule)
  -> (LeafId -> Maybe Prop)
  -> CertOk
  -> DefeatPolicy
  -> RAttack
  -> Either CheckError ()
checkAttack pI gamma certOk dp k =
  case inferSupport pI gamma certOk LocRoot (rSource k) of
    Left e -> Left e
    Right result -> checkAttackTarget pI gamma dp k (srConclusion result)
