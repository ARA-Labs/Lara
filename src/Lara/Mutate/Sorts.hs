-- | The signature-family mutation operators (@lara-core\@0.2@, #89 D10).
--
-- Spec §10.1 states its own invariant: /every class must be exercised by at
-- least one rejected example and one mutation./ R2 satisfied neither — the
-- suite had __zero__ @reject-R2@ rows across all 369 mutants and no
-- @examples/@ directory produced one — so this pass has to __grow__ the suite,
-- not merely re-run it. One operator per clause of the amended class:
--
-- +----------------------+------------------------------------------------+----------+
-- | operator             | mutation                                       | expected |
-- +======================+================================================+==========+
-- | @undeclared-pred@    | rewrite an atom's head to an undeclared 'Pred' | R2       |
-- | @wrong-pred-arity@   | drop or duplicate an atom argument             | R2       |
-- | @wrong-arg-sort@     | swap in a well-sorted term of a /different/    | R2       |
-- |                      | sort taken from the same unit                   |          |
-- | @undeclared-con@     | rewrite a 'TCon' head to an undeclared 'FunSym'| R2       |
-- | @wrong-theta-sort@   | swap a θ range term at a declared parameter     | R2       |
-- | @out-of-scope-var@   | rewrite a rule pattern variable off 'ruleParams'| R12     |
-- +----------------------+------------------------------------------------+----------+
--
-- Two of the six are load-bearing beyond coverage:
--
--   * @wrong-theta-sort@ is the __per-instance half's own witness__. Under a
--     static-only stage-2 design it would be /accepted/, so it is the
--     executable statement of the argument that the θ-range check has to exist:
--     θ's range terms are authored, not drawn from Γ, and a rule instance's
--     conclusion is θ-instantiated, so an ill-sorted range value produces an
--     ill-sorted argument conclusion no other stage sees.
--   * @out-of-scope-var@ is the witness for the §4.1 rule well-formedness
--     that "Lara.Policy" now enforces as R12's second arm. That enforcement is
--     new, and it must not land witness-free the way R2 once did.
--
-- The Γ/θ operators (@undeclaredPredSites@ through @outOfScopeVarSites@)
-- mutate static material or a θ and leave Σ intact. The dedicated closeout
-- fixtures (@duplicateSortSites@ through @predUndeclaredSortSites@) mutate Σ
-- itself, one per well-formedness clause, to exercise the integrated stage-2
-- boundary.
module Lara.Mutate.Sorts
  ( undeclaredPredSites
  , wrongPredAritySites
  , wrongArgSortSites
  , undeclaredConSites
  , wrongThetaSortSites
  , outOfScopeVarSites
  , duplicateSortSites
  , shadowBaseSortSites
  , duplicateConSites
  , duplicatePredSites
  , conUndeclaredSortSites
  , predUndeclaredSortSites
  ) where

import Lara.AST
import Lara.Diagnostics (Constituent (..))
import Lara.Prop (Prop (..), Term (..))
import Lara.Sigma (ConSig (..), PredSig (..), Sigma (..), Sort (..), SortName (..), sortOf)
import Lara.Sigma.WellSorted (ruleParamSorts)

-- | The seeded ground-truth constituent of every signature-family mutant.
-- "Lara.Diagnostics".@locate@ places a stage-2 failure at the policy — a sort
-- failure is always a fact about the declared signature or about material read
-- under it — so that is the location the manifest records.
sigmaLoc :: Constituent
sigmaLoc = CPolicy

-- | A mutation site: the rejection class it must produce, its seeded
-- ground-truth constituent, and the transformation.
--
-- The class is a bare 'RejectClass' rather than "Lara.Mutate"\'s @Expected@ so
-- that this module sits /below/ the operator vocabulary in the module graph:
-- "Lara.Mutate" owns the operator names and wraps these sites.
type Site = (RejectClass, Constituent, Unit -> Unit)

-- ---------------------------------------------------------------------------
-- Sigma well-formedness fixtures
-- ---------------------------------------------------------------------------

-- | R2: the same declared sort appears twice.
duplicateSortSites :: Unit -> [Site]
duplicateSortSites _ =
  [ (R2, sigmaLoc, mapSigma (\sg -> sg{sigmaSorts = duplicate : duplicate : sigmaSorts sg}))
  ]
  where
    duplicate = SortName "mut_dup_sort"

-- | R2: a declaration shadows the reserved base sort @Num@.
shadowBaseSortSites :: Unit -> [Site]
shadowBaseSortSites _ =
  [ (R2, sigmaLoc, mapSigma (\sg -> sg{sigmaSorts = SortName "Num" : sigmaSorts sg}))
  ]

-- | R2: the same constructor symbol is declared twice.
duplicateConSites :: Unit -> [Site]
duplicateConSites _ =
  [ (R2, sigmaLoc, mapSigma (\sg -> sg{sigmaCons = duplicate : duplicate : sigmaCons sg}))
  ]
  where
    duplicate = ConSig (FunSym "mut_dup_con") [] SortNum

-- | R2: the same predicate symbol is declared twice.
duplicatePredSites :: Unit -> [Site]
duplicatePredSites _ =
  [ (R2, sigmaLoc, mapSigma (\sg -> sg{sigmaPreds = duplicate : duplicate : sigmaPreds sg}))
  ]
  where
    duplicate = PredSig (Pred "mut_dup_pred") []

-- | R2: a constructor signature names an undeclared result sort.
conUndeclaredSortSites :: Unit -> [Site]
conUndeclaredSortSites _ =
  [ ( R2
    , sigmaLoc
    , mapSigma
        ( \sg ->
            sg
              { sigmaCons =
                  ConSig
                    (FunSym "mut_bad_con_sort")
                    []
                    (SortDecl (SortName "mut_missing_sort"))
                    : sigmaCons sg
              }
        )
    )
  ]

-- | R2: a predicate signature names an undeclared argument sort.
predUndeclaredSortSites :: Unit -> [Site]
predUndeclaredSortSites _ =
  [ ( R2
    , sigmaLoc
    , mapSigma
        ( \sg ->
            sg
              { sigmaPreds =
                  PredSig
                    (Pred "mut_bad_pred_sort")
                    [SortDecl (SortName "mut_missing_sort")]
                    : sigmaPreds sg
              }
        )
    )
  ]

mapSigma :: (Sigma -> Sigma) -> Unit -> Unit
mapSigma f u = u{unitSigma = f (unitSigma u)}

-- ---------------------------------------------------------------------------
-- Ground-term inventory
-- ---------------------------------------------------------------------------

-- | Every ground argument term the unit mentions, with its sort under the
-- unit's own Σ. The source of replacement terms for the two sort-swap
-- operators: a swap has to be __well-sorted but differently sorted__, or the
-- mutant would be exercising @undeclared-con@ instead.
sortedTerms :: Unit -> [(Term, Sort)]
sortedTerms u =
  [ (t, s)
  | t <- candidates
  , Right s <- [sortOf (unitSigma u) t]
  ]
  where
    candidates =
      concat
        [ ts | (_, Prop _ ts) <- unitLeaves u ]
        ++ concat [ts | Prop _ ts <- unitQueries u]
        ++ [t | (_, w) <- unitArgs u, (_, t) <- substsOf w]

substsOf :: SupportTerm -> [(Param, Term)]
substsOf (SLeaf _) = []
substsOf (SRule _ theta ws d _ _) =
  theta ++ concatMap substsOf ws ++ concatMap (substsOf . snd) d

-- | A term whose sort differs from the given one.
otherSorted :: Unit -> Sort -> Maybe Term
otherSorted u s = case [t | (t, s') <- sortedTerms u, s' /= s] of
  t : _ -> Just t
  [] -> Nothing

-- | Rewrite the proposition of the @i@-th declared leaf.
mapLeaf :: Int -> (Prop -> Prop) -> Unit -> Unit
mapLeaf i f u =
  u{unitLeaves = [(l, if j == i then f p else p) | (j, (l, p)) <- zip [0 :: Int ..] (unitLeaves u)]}

-- ---------------------------------------------------------------------------
-- The operators
-- ---------------------------------------------------------------------------

-- | R2: an undeclared predicate head. By the class boundary (#89 §2.3 rule 1)
-- an undeclared /symbol/ is R2, not R1 — R1 is about declaration identifiers
-- (leaf, argument, rule, question, backend, policy), and symbols have never
-- been in its list.
undeclaredPredSites :: Unit -> [Site]
undeclaredPredSites u =
  [ (R2, sigmaLoc, mapLeaf i (\(Prop _ ts) -> Prop (Pred "mut_undeclared_pred") ts))
  | (i, _) <- zip [0 :: Int ..] (unitLeaves u)
  ]

-- | R2: arity mismatch against Σ — already the frozen spec text, and never
-- enforced before. Dropping the last argument is preferred over duplicating one
-- because it also exercises the shorter-than-declared direction.
wrongPredAritySites :: Unit -> [Site]
wrongPredAritySites u =
  [ (R2, sigmaLoc, mapLeaf i (\(Prop p args) -> Prop p (init args)))
  | (i, (_, Prop _ ts)) <- zip [0 :: Int ..] (unitLeaves u)
  , not (null ts)
  ]

-- | R2: an argument of the wrong sort. The replacement is a term the unit
-- already contains, so the mutant is a single-defect /sort/ error and not an
-- undeclared-symbol error wearing a different name.
wrongArgSortSites :: Unit -> [Site]
wrongArgSortSites u =
  [ (R2, sigmaLoc, mapLeaf i (replaceArg k t))
  | (i, (_, Prop _ ts)) <- zip [0 :: Int ..] (unitLeaves u)
  , (k, arg) <- zip [0 :: Int ..] ts
  , Right s <- [sortOf (unitSigma u) arg]
  , Just t <- [otherSorted u s]
  ]
  where
    replaceArg k t (Prop p ts) = Prop p [if j == k then t else x | (j, x) <- zip [0 :: Int ..] ts]

-- | R2: an undeclared constructor head. Chooses a leaf argument that /is/ a
-- constructor application, so the defect is the head symbol and nothing else.
undeclaredConSites :: Unit -> [Site]
undeclaredConSites u =
  [ (R2, sigmaLoc, mapLeaf i (renameCon k))
  | (i, (_, Prop _ ts)) <- zip [0 :: Int ..] (unitLeaves u)
  , (k, TCon _ _) <- zip [0 :: Int ..] ts
  ]
  where
    renameCon k (Prop p ts) =
      Prop p [if j == k then rename x else x | (j, x) <- zip [0 :: Int ..] ts]
    rename (TCon _ args) = TCon (FunSym "mut_undeclared_con") args
    rename t = t

-- | R2, the per-instance half's witness: a θ binding at a __declared__
-- parameter whose term has the wrong sort.
--
-- The key must be in @ruleParams@ and must have a derived sort. A key /off/ the
-- parameter list is R3's business (#89 §2.3 rule 3) and is exactly what
-- @wrong-subst-domain@ already tests — keeping the two apart is what makes the
-- reclassification delta over the pre-existing suite empty.
wrongThetaSortSites :: Unit -> [Site]
wrongThetaSortSites u =
  [ (R2, sigmaLoc, rewriteTheta i x t)
  | (i, (_, w)) <- zip [0 :: Int ..] (unitArgs u)
  , (rid, theta) <- topInstance w
  , r <- ruleWith rid
  , Right env <- [ruleParamSorts (unitSigma u) r]
  , (x, old) <- theta
  , x `elem` ruleParams r
  , Just s <- [lookup x env]
  , Right s' <- [sortOf (unitSigma u) old]
  , s' == s
  , Just t <- [otherSorted u s]
  ]
  where
    topInstance (SRule rid theta _ _ _ _) = [(rid, theta)]
    topInstance _ = []
    ruleWith rid = [r | r <- unitRules u, ruleId r == rid]
    rewriteTheta i x t un =
      un
        { unitArgs =
            [ (aid, if j == i then setTheta w else w)
            | (j, (aid, w)) <- zip [0 :: Int ..] (unitArgs un)
            ]
        }
      where
        setTheta (SRule rid theta ws d hs a) =
          SRule rid [(y, if y == x then t else v) | (y, v) <- theta] ws d hs a
        setTheta w = w

-- | R12, the §4.1 witness: a rule pattern variable that is not among the
-- rule's declared parameters.
--
-- This is __policy__ well-formedness, not a sort failure: the mutated pattern
-- is perfectly well-sorted, the variable simply is not in scope. Keeping it
-- R12 is what leaves R2 purely about sorts (#89 D-2).
outOfScopeVarSites :: Unit -> [Site]
outOfScopeVarSites u =
  [ (R12, CPolicy, rewriteRule i)
  | (i, r) <- zip [0 :: Int ..] (unitRules u)
  , hasVar (ruleConclusion r)
  ]
  where
    hasVar (AtomPat _ ps) = any isVar ps
    isVar (PVar _) = True
    isVar (PCon _ ps) = any isVar ps
    isVar (PLit _) = False
    rewriteRule i un =
      un
        { unitRules =
            [ if j == i then r{ruleConclusion = escape (ruleConclusion r)} else r
            | (j, r) <- zip [0 :: Int ..] (unitRules un)
            ]
        }
    escape (AtomPat p ps) = AtomPat p (renameFirst ps)
    renameFirst [] = []
    renameFirst (p : rest)
      | isVar p = PVar (Param "mut_out_of_scope") : rest
      | otherwise = p : renameFirst rest
