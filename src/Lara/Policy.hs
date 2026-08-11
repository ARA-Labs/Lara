-- | Executable policy well-formedness (spec §4, §8.1) — the Haskell mirror of
-- @lean/Lara/Policy.lean@.
--
-- The strict-reachable patterns are exactly the conclusions of strict rules
-- (the finite presentation of the spec's least set — Lean
-- @strictReachable_iff_mem@). 'wfB' decides the §8.1 Path-B judgment: no
-- strict-reachable conclusion pattern may overlap at the instance level with
-- either side of a declared @contrary@ pair. 'firstViolation' is the located
-- R12 diagnostic payload, retaining the offending rule id and contrary pair
-- (Lean @firstViolation?@ / @Violation@).
--
-- Duplicate rule identifiers are detected by 'firstDuplicateRuleId' (Lean
-- @firstDuplicateRuleId?@); the public 'Lara.Check.checkUnit' flow rejects
-- them before running this R12 validator, before any program checking.
--
-- The instance-overlap check is the conservative structural unifiability test
-- of the Lean development ('patMayOverlap'): variables are wildcards, literals
-- are compared after normalization ('nfTerm'), and constructor\/predicate
-- symbols and arities must agree. Repeated-variable equality constraints are
-- deliberately ignored, so the check can reject a safe policy but cannot
-- accept two patterns with canonically equivalent ground instances — the
-- one-sided guarantee Path B requires (Lean @aPatMayOverlap_of_instances@).
module Lara.Policy
  ( -- * Duplicate rule identifiers
    DuplicateRuleId (..)
  , firstDuplicateRuleId
    -- * Rule lookup
  , RuleLookup
  , lookupRule
    -- * Strict-reachable patterns
  , strictConclusions
    -- * Conservative instance overlap
  , patMayOverlap
  , patsMayOverlap
  , aPatMayOverlap
    -- * The §8.1 validator and the §4.1 rule-scope validator
  , RuleSite (..)
  , Violation (..)
  , touchingPair
  , firstOutOfScope
  , firstViolation
  , wfB
  ) where

import Lara.AST
import Lara.Prop (nfTerm)

-- ---------------------------------------------------------------------------
-- Duplicate rule identifiers
-- ---------------------------------------------------------------------------

-- | A duplicate rule identifier, with both declaration positions retained for
-- the decode-boundary diagnostic (mirrors Lean @Policy.DuplicateRule@ (renamed to avoid clashing with the @Rejection@ constructor)).
data DuplicateRuleId = DuplicateRuleId
  { drId :: RuleId
  , drFirstIndex :: Int
  , drDuplicateIndex :: Int
  }
  deriving (Eq, Show)

-- | The first duplicate identifier in declaration order: the outer scan fixes
-- the first declaration and the inner scan its earliest later duplicate
-- (mirrors Lean @firstDuplicateRuleId?@). 'Nothing' iff the id list is
-- duplicate-free (Lean @firstDuplicateRuleId?_none_iff@).
firstDuplicateRuleId :: [Rule] -> Maybe DuplicateRuleId
firstDuplicateRuleId = go 0
  where
    go _ [] = Nothing
    go i (r : rest) = case firstEqual (ruleId r) (i + 1) rest of
      Just j -> Just (DuplicateRuleId (ruleId r) i j)
      Nothing -> go (i + 1) rest
    firstEqual _ _ [] = Nothing
    firstEqual rid j (r : rest)
      | ruleId r == rid = Just j
      | otherwise = firstEqual rid (j + 1) rest

-- ---------------------------------------------------------------------------
-- Rule lookup
-- ---------------------------------------------------------------------------

-- | The rule context @Pi@ as the checkers consume it: a total lookup into the
-- policy's declared rules (mirrors Lean @Pi : RuleId → Option Rule@).
type RuleLookup = RuleId -> Maybe Rule

-- | Declaration-order (first-match) rule lookup (mirrors Lean
-- @lookupRuleDecl@). Raw policies can contain duplicates; accepted policies
-- rule them out ('firstDuplicateRuleId') before relying on this function.
lookupRule :: [Rule] -> RuleLookup
lookupRule [] _ = Nothing
lookupRule (r : rest) rid
  | ruleId r == rid = Just r
  | otherwise = lookupRule rest rid

-- ---------------------------------------------------------------------------
-- Strict-reachable patterns
-- ---------------------------------------------------------------------------

-- | The finite list used by the executable check: the conclusions of the
-- declared strict rules (mirrors Lean @strictConclusions@; by
-- @strictReachable_iff_mem@ this denotes exactly the spec's least set).
strictConclusions :: [Rule] -> [AtomPat]
strictConclusions rules =
  [ruleConclusion r | r <- rules, ruleMode r == Strict]

-- ---------------------------------------------------------------------------
-- Conservative instance overlap (mirrors the Lean @patMayOverlap@ family)
-- ---------------------------------------------------------------------------

-- | May two patterns share a canonically equivalent ground instance?
-- Conservative: variables are wildcards; literals compare after 'nfTerm'
-- (numbers via @canonNum@, strings verbatim), and constructor patterns must
-- agree on symbol and overlap pointwise. Mirrors Lean @patMayOverlap@ on
-- every wire-decoder-produced pattern: 'PLit' folds Lean's separate @.num@ /
-- @.str@ cases (distinct constructors never compare equal under 'nfTerm', so
-- a number never overlaps a string), and a literal never overlaps a
-- constructor pattern (the final catch-all).
patMayOverlap :: Pat -> Pat -> Bool
patMayOverlap (PVar _) _ = True
patMayOverlap _ (PVar _) = True
patMayOverlap (PLit a) (PLit b) = nfTerm a == nfTerm b
patMayOverlap (PCon k ps) (PCon l qs) = k == l && patsMayOverlap ps qs
patMayOverlap _ _ = False

-- | Argument lists overlap pointwise; a length mismatch is no overlap.
patsMayOverlap :: [Pat] -> [Pat] -> Bool
patsMayOverlap [] [] = True
patsMayOverlap (p : ps) (q : qs) = patMayOverlap p q && patsMayOverlap ps qs
patsMayOverlap _ _ = False

-- | Atom patterns overlap when their predicates agree and their argument
-- lists overlap (mirrors Lean @aPatMayOverlap@).
aPatMayOverlap :: AtomPat -> AtomPat -> Bool
aPatMayOverlap (AtomPat p ps) (AtomPat q qs) =
  p == q && patsMayOverlap ps qs

-- ---------------------------------------------------------------------------
-- The §8.1 validator
-- ---------------------------------------------------------------------------

-- | Which pattern of a rule a §4.1 scope violation sits in. Exceptions are
-- indexed into the policy's own @exception@ list, since they are declared
-- outside the @rule@ block.
data RuleSite
  = SitePremise Int
  | SiteConclusion
  | SiteAnswer QuestionId
  | SiteException Int
  deriving (Eq, Show)

-- | Located R12 payload (mirrors Lean @Policy.Violation@).
--
-- Two arms, one class. Spec §8.1 Path B and spec §4.1 rule well-formedness are
-- both /policy/ well-formedness — a policy the checker may not read as patterns
-- — so they share R12 and this stage rather than splitting a frozen class. R2
-- stays purely about sorts (#89 D-2): an out-of-scope pattern variable is
-- perfectly well-sorted, it is simply not in scope.
data Violation
  = -- | §8.1 Path B: a strict rule's conclusion pattern may overlap a declared
    -- contrary side at the instance level
    StrictContraryOverlap RuleId AtomPat Contrary
  | -- | §4.1: a pattern variable outside the rule's declared parameters
    OutOfScopeParam RuleId RuleSite Param
  deriving (Eq, Show)

-- | The first §4.1 scope violation in declaration order: rules in list order,
-- and within a rule its premises, conclusion, and question answers; then the
-- policy's exceptions in list order, each against its own rule's parameters.
--
-- An exception naming an undeclared rule is __not__ a scope violation here: its
-- rule id is R1's business at the support stage, and every variable is
-- vacuously out of an empty parameter list, which would turn one missing
-- declaration into a misleading R12.
firstOutOfScope :: [Rule] -> [Exception] -> Maybe Violation
firstOutOfScope rules exceptions =
  firstJust (map ruleScan rules ++ map exceptionScan (zip [0 ..] exceptions))
  where
    ruleScan r =
      firstJust $
        [ OutOfScopeParam (ruleId r) (SitePremise i) <$> escapee r a
        | (i, a) <- zip [0 ..] (rulePremises r)
        ]
          ++ [OutOfScopeParam (ruleId r) SiteConclusion <$> escapee r (ruleConclusion r)]
          ++ [ OutOfScopeParam (ruleId r) (SiteAnswer (questionId q)) <$> escapee r (questionAnswer q)
             | q <- ruleQuestions r
             ]
    exceptionScan (i, e) = case lookupRule rules (exceptionRule e) of
      Nothing -> Nothing
      Just r -> OutOfScopeParam (exceptionRule e) (SiteException i) <$> escapee r (exceptionAtom e)
    escapee r (AtomPat _ ps) = firstJust (map (patEscapee (ruleParams r)) ps)
    patEscapee params p = case p of
      PVar x
        | x `elem` params -> Nothing
        | otherwise -> Just x
      PLit _ -> Nothing
      PCon _ ps -> firstJust (map (patEscapee params) ps)

firstJust :: [Maybe a] -> Maybe a
firstJust = foldr (\m acc -> maybe acc Just m) Nothing

-- | The first declared contrary pair either of whose sides may overlap the
-- given strict conclusion (mirrors Lean @touchingPair?@).
touchingPair :: AtomPat -> [Contrary] -> Maybe Contrary
touchingPair _ [] = Nothing
touchingPair p (c@(Contrary a b) : rest)
  | aPatMayOverlap p a || aPatMayOverlap p b = Just c
  | otherwise = touchingPair p rest

-- | The single declaration-order diagnostic scan (mirrors Lean
-- @firstViolation?@): spec §4.1 rule scope first, then spec §8.1 Path B over
-- strict rules and their contrary pairs.
--
-- Scope runs first because Path B reads a rule's conclusion /as a pattern over
-- its parameters/; a conclusion mentioning a variable the rule never declared
-- is not a pattern the overlap test is entitled to interpret.
firstViolation :: [Rule] -> [Contrary] -> [Exception] -> Maybe Violation
firstViolation rules contraries exceptions =
  case firstOutOfScope rules exceptions of
    Just v -> Just v
    Nothing -> go rules
  where
    go [] = Nothing
    go (r : rest)
      | ruleMode r == Strict =
          case touchingPair (ruleConclusion r) contraries of
            Just c -> Just (StrictContraryOverlap (ruleId r) (ruleConclusion r) c)
            Nothing -> go rest
      | otherwise = go rest

-- | Executable @wf(Pi)@ (spec §4.1 + §8.1), derived from the same located scan
-- used for diagnostics (mirrors Lean @wfB@ \/ @wfB_iff@).
wfB :: [Rule] -> [Contrary] -> [Exception] -> Bool
wfB rules contraries exceptions = case firstViolation rules contraries exceptions of
  Nothing -> True
  Just _ -> False
