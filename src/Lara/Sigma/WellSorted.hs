-- | Well-sortedness of the checker-boundary objects under @Σ@ — the pattern
-- half of "Lara.Sigma" and the decision procedure "Lara.Check" runs as stage 2
-- (rejection class __R2__).
--
-- The split from "Lara.Sigma" is forced by the module graph, not by design:
-- 'Lara.AST.Unit' carries a 'Sigma' field, so "Lara.Sigma" cannot see
-- "Lara.AST". Everything here is the same deliverable.
--
-- == Derived parameter sorts (spec §3.4)
--
-- Rule parameter sorts are __derived, not declared__. Under a well-formed Σ
-- every parameter occupies sorted positions in its own rule's patterns, so its
-- sort is the unique sort of all its occurrences; disagreeing occurrences are
-- the reject 'PatParamSort'. A parameter with no pattern occurrence is
-- /unconstrained/ — its θ bindings are checked for well-sortedness but against
-- no expected sort, because no instantiated atom can mention it. This is why
-- there is no ninth wire field in the @rules@ section and no stored 'Rule'
-- field.
--
-- == What the stage does not decide (spec §10.1 class boundary)
--
--   * an undeclared /symbol/ — predicate head or constructor — is R2, not R1:
--     R1 is about declaration identifiers (leaf, argument, rule, question,
--     backend, policy) and symbols have never been in its list;
--   * a substitution whose /domain/ is wrong is R3: this stage checks the sorts
--     of θ's range terms at keys that /are/ declared parameters and says
--     nothing about whether θ covers every parameter;
--   * an instance whose rule id does not resolve in the policy is R1's
--     business: 'unitSortError' quantifies only over instances whose rule id
--     resolves, so a hidden rule stays an R1 support failure rather than
--     becoming a stage-2 lookup error;
--   * an out-of-scope pattern /variable/ is policy well-formedness (R12,
--     "Lara.Policy"), not a sort failure: this stage happily derives a sort for
--     it.
--
-- Mirrors @lean\/Lara\/Sigma.lean@.
module Lara.Sigma.WellSorted
  ( -- * Derived parameter sorts
    ParamSorts
  , PatFault (..)
  , checkPat
  , checkAPat
  , ruleParamSorts
    -- * Located R2 diagnostics
  , SortError (..)
  , sortErrorFault
    -- * The stage
  , sigmaStaticError
  , sigmaSubstError
  , unitSortError
  , unitWellSorted
  ) where

import Lara.AST
import Lara.Sigma

-- ---------------------------------------------------------------------------
-- Derived parameter sorts
-- ---------------------------------------------------------------------------

-- | The sorts derived for a pattern scope, in first-occurrence order. An
-- association list, like 'Lara.AST.Subst': scopes are tiny and the order is
-- what makes the diagnostic deterministic.
type ParamSorts = [(Param, Sort)]

-- | A pattern-level sort failure: either a ground fault or two occurrences of
-- one parameter demanding different sorts.
data PatFault
  = PatGround SortFault
  | -- | parameter, sort derived from its first occurrence, sort demanded here
    PatParamSort Param Sort Sort
  deriving (Eq, Show)

-- | Check one pattern against the sort its position demands, extending the
-- derived parameter environment.
checkPat :: Sigma -> ParamSorts -> Sort -> Pat -> Either PatFault ParamSorts
checkPat sg env expected pat = case pat of
  PVar x -> case lookup x env of
    Nothing -> Right (env ++ [(x, expected)])
    Just s
      | s == expected -> Right env
      | otherwise -> Left (PatParamSort x s expected)
  PLit t -> case sortOf sg t of
    Left f -> Left (PatGround f)
    Right actual
      | actual == expected -> Right env
      | otherwise -> Left (PatGround (FaultArgSort expected actual))
  PCon k ps -> case lookupCon sg k of
    Nothing -> Left (PatGround (FaultUndeclaredCon k))
    Just sig
      | length ps /= length (conArgs sig) ->
          Left (PatGround (FaultConArity k (length (conArgs sig)) (length ps)))
      | conResult sig /= expected ->
          Left (PatGround (FaultArgSort expected (conResult sig)))
      | otherwise -> checkPats sg env (conArgs sig) ps

checkPats :: Sigma -> ParamSorts -> [Sort] -> [Pat] -> Either PatFault ParamSorts
checkPats _ env [] [] = Right env
checkPats sg env (s : ss) (p : ps) = do
  env' <- checkPat sg env s p
  checkPats sg env' ss ps
-- Unreachable: every caller checks the arity first.
checkPats _ env _ _ = Right env

-- | Check one atom pattern, extending the derived parameter environment.
checkAPat :: Sigma -> ParamSorts -> AtomPat -> Either PatFault ParamSorts
checkAPat sg env (AtomPat p ps) = case lookupPred sg p of
  Nothing -> Left (PatGround (FaultUndeclaredPred p))
  Just sig
    | length ps /= length (predArgs sig) ->
        Left (PatGround (FaultPredArity p (length (predArgs sig)) (length ps)))
    | otherwise -> checkPats sg env (predArgs sig) ps

checkAPats :: Sigma -> ParamSorts -> [AtomPat] -> Either PatFault ParamSorts
checkAPats _ env [] = Right env
checkAPats sg env (a : as) = do
  env' <- checkAPat sg env a
  checkAPats sg env' as

-- | Derive a rule's parameter sorts from its own patterns, in the fixed order
-- premises, conclusion, question answers. Exception atoms extend this
-- environment at their own declaration site ('sigmaStaticError') rather than
-- here, so an exception naming an unknown rule is still checked.
ruleParamSorts :: Sigma -> Rule -> Either PatFault ParamSorts
ruleParamSorts sg r = do
  env1 <- checkAPats sg [] (rulePremises r)
  env2 <- checkAPat sg env1 (ruleConclusion r)
  checkAPats sg env2 (map questionAnswer (ruleQuestions r))

-- ---------------------------------------------------------------------------
-- Located R2 diagnostics
-- ---------------------------------------------------------------------------

-- | A located stage-2 failure. Every arm is rejection class R2.
data SortError
  = -- | Σ itself is malformed
    SEMalformedSigma SigmaFault
  | -- | a rule's premise, conclusion, or answer patterns
    SERule RuleId PatFault
  | -- | @unitExceptions !! i@
    SEException Int PatFault
  | -- | @unitContraries !! i@
    SEContrary Int PatFault
  | -- | the @j@-th proposition of the named theory
    SETheory TheoryDigest Int SortFault
  | -- | a leaf conclusion in Γ
    SELeaf LeafId SortFault
  | -- | @unitQueries !! i@
    SEQuery Int SortFault
  | -- | a θ range term at a declared parameter of a resolvable rule
    SESubst ArgId RuleId Param SortFault
  deriving (Eq, Show)

-- | The ground fault underlying a located error, when there is one. @Nothing@
-- for a malformed Σ and for a parameter-sort disagreement, which are not
-- faults /of a term/.
sortErrorFault :: SortError -> Maybe SortFault
sortErrorFault e = case e of
  SEMalformedSigma _ -> Nothing
  SERule _ pf -> groundOf pf
  SEException _ pf -> groundOf pf
  SEContrary _ pf -> groundOf pf
  SETheory _ _ f -> Just f
  SELeaf _ f -> Just f
  SEQuery _ f -> Just f
  SESubst _ _ _ f -> Just f
  where
    groundOf (PatGround f) = Just f
    groundOf (PatParamSort _ _ _) = Nothing

-- ---------------------------------------------------------------------------
-- The static half
-- ---------------------------------------------------------------------------

-- | Σ against the policy and the context: Σ-well-formedness, then every rule,
-- exception, contrary, theory proposition, leaf conclusion, and query — one
-- pass, no support terms.
--
-- Contrary pairs carry no parameter scope (their variables are universally
-- quantified, "Lara.Attack".@matchPat@), so each /pair/ is checked under one
-- fresh environment shared by both sides: the same variable must have the same
-- sort on the left and the right.
sigmaStaticError :: Unit -> Maybe SortError
sigmaStaticError u =
  firstJust
    [ SEMalformedSigma <$> sigmaFault sg
    , firstJust [SERule (ruleId r) <$> leftOf (ruleParamSorts sg r) | r <- rules]
    , firstJust
        [ SEException i <$> leftOf (checkAPat sg (envOf (exceptionRule e)) (exceptionAtom e))
        | (i, e) <- zip [0 ..] (unitExceptions u)
        ]
    , firstJust
        [ SEContrary i <$> leftOf (checkAPats sg [] [a, b])
        | (i, Contrary a b) <- zip [0 ..] (unitContraries u)
        ]
    , firstJust
        [ SETheory d j <$> sortCheckProp sg p
        | (d, ps) <- unitTheories u
        , (j, p) <- zip [0 ..] ps
        ]
    , firstJust [SELeaf l <$> sortCheckProp sg p | (l, p) <- unitLeaves u]
    , firstJust [SEQuery i <$> sortCheckProp sg p | (i, p) <- zip [0 ..] (unitQueries u)]
    ]
  where
    sg = unitSigma u
    rules = unitRules u
    -- The derived environment of a rule that itself passed; a rule that failed
    -- has already produced the reported error, and an exception naming an
    -- unknown rule is checked in the empty environment.
    envOf rid = case [r | r <- rules, ruleId r == rid] of
      r : _ -> either (const []) id (ruleParamSorts sg r)
      [] -> []

-- ---------------------------------------------------------------------------
-- The per-instance half
-- ---------------------------------------------------------------------------

-- | Σ against @unitArgs@: for every rule instance whose rule id resolves and
-- every @(X, t)@ in its θ, @t@ must be well-sorted, and when @X@ is a declared
-- parameter with a derived sort, @sortOf t@ must equal it.
--
-- __Why this is required.__ θ's range terms are /authored/, not drawn from Γ. A
-- rule instance's conclusion is θ-instantiated and need not match any leaf, so
-- an ill-sorted range value produces an ill-sorted argument conclusion that no
-- other stage catches. Premises escape only incidentally, via R4's @≡@-match
-- against a leaf the static half already sorted.
sigmaSubstError :: Unit -> Maybe SortError
sigmaSubstError u =
  firstJust [walk a w | (a, w) <- unitArgs u]
  where
    sg = unitSigma u
    rules = unitRules u

    walk _ (SLeaf _) = Nothing
    walk a (SRule rid theta prems dis _ _) =
      firstJust
        ( [instanceError a rid theta]
            ++ map (walk a) prems
            ++ map (walk a . snd) dis
        )

    instanceError a rid theta = case [r | r <- rules, ruleId r == rid] of
      -- An unresolved rule id is R1's business at the support stage.
      [] -> Nothing
      r : _ ->
        let env = either (const []) id (ruleParamSorts sg r)
         in firstJust [bindingError a rid r env x t | (x, t) <- theta]

    bindingError a rid r env x t
      | x `notElem` ruleParams r = Nothing
      | otherwise = SESubst a rid x <$> bindingFault env x t

    bindingFault env x t = case sortOf sg t of
      Left f -> Just f
      Right actual -> case lookup x env of
        Nothing -> Nothing -- unconstrained parameter: no expected sort
        Just expected
          | actual == expected -> Nothing
          | otherwise -> Just (FaultArgSort expected actual)

-- ---------------------------------------------------------------------------
-- The stage
-- ---------------------------------------------------------------------------

-- | Stage 2 of 'Lara.Check.checkUnit': the static half, then the per-instance
-- half. 'Nothing' iff the unit is well-sorted under its own Σ.
unitSortError :: Unit -> Maybe SortError
unitSortError u = firstJust [sigmaStaticError u, sigmaSubstError u]

-- | Decidable whole-unit well-sortedness, derived from the located scan.
unitWellSorted :: Unit -> Bool
unitWellSorted u = case unitSortError u of
  Nothing -> True
  Just _ -> False

-- ---------------------------------------------------------------------------
-- Helpers
-- ---------------------------------------------------------------------------

leftOf :: Either a b -> Maybe a
leftOf (Left a) = Just a
leftOf (Right _) = Nothing

firstJust :: [Maybe a] -> Maybe a
firstJust = foldr (\m acc -> maybe acc Just m) Nothing
