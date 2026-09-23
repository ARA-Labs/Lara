-- | Navigation and rewriting helpers shared by the site enumerators, split
-- out of "Lara.Mutate.Sites" alongside the certificate family; see
-- @docs\/mutate-module-ownership-decision.md@).
--
-- These were private to "Lara.Mutate.Sites" before the split and stay
-- library-internal: the module is an @other-module@, and its consumers are the
-- site enumerators — "Lara.Mutate.Sites", "Lara.Mutate.Sites.Cert",
-- "Lara.Mutate.Sites.Conflict", and "Lara.Mutate.Sites.Localize" — plus
-- "Lara.Mutate.Sorts", which is the one consumer that imports the index-space
-- newtypes alone.
--
-- Nothing here inspects an operator or an 'Lara.Mutate.Expected' — these are
-- purely structural. The load-bearing ordering invariant lives with the
-- enumerators that consume them: 'occurrences' fixes a deterministic traversal
-- order, and 'ruleSites' \/ 'leafSites' preserve it, so a change to the
-- traversal here moves committed corpus bytes.
--
-- __Two index spaces__. The checker runs on the §4.3 quarantine of the
-- declared unit, and its verdict names /checked/ indices; the mutation rewrite
-- edits the /declared/ unit. 'ruleSites' and 'leafSites' therefore read a
-- 'Prune' and carry both: sites are drawn from the checked argument list (a
-- mutation into a pruned argument is an accepting no-op the checker never
-- sees), the published index is the checked one, and the paired declared index
-- ('Lara.Blocked.retainedIndices') is the one the rewrite must edit. A retained
-- argument's term is exactly its declared term — the prune filters whole
-- arguments — so positions computed here are valid in both units.
--
-- The two spaces are 'CheckedIx' and 'DeclaredIx', not two bare 'Int's, so a
-- transposed pair is a type error rather than a silently corrupted answer key
-- (the repo's \"separate namespaces get separate types\" rule).
--
-- They are __constructed__ either by reading a retained-index list — the only
-- thing that may /pair/ the two spaces ('argSites' and 'attackSites' here,
-- 'Lara.Mutate.Sorts.retainedLeafDecls' and @retainedArgDecls@ there) — or
-- directly in checked space from a measurement of the checked unit, which pairs
-- nothing — 'Lara.Mutate.Sites.unlicensedAttackSites' builds
-- @CheckedIx (length (unitAttacks checked))@ for its appended attack, the one
-- such site. They are __unwrapped__ only in these three kinds of place, each of
-- which stays within one space:
--
--   1. Publishing a 'Lara.Diagnostics.Constituent', through 'checkedIx'.
--   2. Inside a rewrite helper that takes a 'DeclaredIx' and edits the declared
--      unit — 'rewriteArg', 'setAttackAt', and 'dropAttackAt' here;
--      'Lara.Mutate.Sorts.mapLeaf' and that module's θ rewrite there.
--   3. Where a 'CheckedIx' indexes the /checked/ unit itself, which crosses no
--      boundary at all: "Lara.Mutate.Sites.Conflict"'s survivor scan
--      (@dropIx (checkedIx ci) checkedAttacks@) is the only such site.
--
-- The invariant is not a count of these sites but what none of them does: pair
-- the two spaces outside a retained-index list.
-- 'Lara.Diagnostics.Constituent' and the 'Lara.Blocked' retained-index lists
-- keep their bare-'Int' APIs.
module Lara.Mutate.Sites.Nav
  ( CheckedIx (..)
  , DeclaredIx (..)
  , occurrences
  , rewriteAt
  , rewriteArg
  , setAttackAt
  , dropAttackAt
  , argSites
  , ruleSites
  , leafSites
  , attackSites
  , ruleOf
  , inequivLeaf
  ) where

import Data.List (find)

import Lara.AST
import Lara.Blocked (Prune, pruneChecked, retainedAttackIndices, retainedIndices)
import Lara.Prop (Prop (..), equiv)

-- | An index into the __checked__ unit — the §4.3 quarantine the checker runs
-- on, and so the space every published 'Lara.Diagnostics.Constituent' index
-- must be in.
newtype CheckedIx = CheckedIx {checkedIx :: Int}
  deriving (Eq, Ord, Show)

-- | An index into the __declared__ unit — the space the mutation rewrite
-- edits, reached from a 'CheckedIx' through the prune's retained-index lists.
newtype DeclaredIx = DeclaredIx {declaredIx :: Int}
  deriving (Eq, Ord, Show)

-- | Every subterm occurrence of a term, keyed by its 'Position'.
occurrences :: SupportTerm -> [(Position, SupportTerm)]
occurrences w = go [] w
  where
    go pos t =
      (reverse pos, t) : case t of
        SLeaf _ -> []
        SRule _ _ ws d _ _ ->
          concat
            [ go (StepPremise i : pos) wi
            | (i, wi) <- zip [0 ..] ws
            ]
            ++ concat
              [ go (StepQuestion q : pos) wq
              | (q, wq) <- d
              ]

-- | Rewrite the subterm at a position (total: an unreachable position is the
-- identity, but sites always come from 'occurrences').
rewriteAt :: Position -> (SupportTerm -> SupportTerm) -> SupportTerm -> SupportTerm
rewriteAt [] f t = f t
rewriteAt (step : rest) f t = case t of
  SLeaf _ -> t
  SRule r theta ws d hs a -> case step of
    StepPremise i ->
      SRule r theta [if j == i then rewriteAt rest f w else w | (j, w) <- zip [0 ..] ws] d hs a
    StepQuestion q ->
      SRule r theta ws [(q', if q' == q then rewriteAt rest f w else w) | (q', w) <- d] hs a

-- | Rewrite one declared argument's term.
rewriteArg :: DeclaredIx -> (SupportTerm -> SupportTerm) -> Unit -> Unit
rewriteArg (DeclaredIx ix) f u =
  u
    { unitArgs =
        [ (aid, if j == ix then f t else t)
        | (j, (aid, t)) <- zip [0 ..] (unitArgs u)
        ]
    }

-- | Replace one declared attack.
setAttackAt :: DeclaredIx -> Attack -> Unit -> Unit
setAttackAt (DeclaredIx ix) k u =
  u{unitAttacks = [if j == ix then k else y | (j, y) <- zip [0 ..] (unitAttacks u)]}

-- | Delete one declared attack.
dropAttackAt :: DeclaredIx -> Unit -> Unit
dropAttackAt (DeclaredIx ix) u =
  u{unitAttacks = [y | (j, y) <- zip [0 ..] (unitAttacks u), j /= ix]}

-- | The checked unit's arguments with both indices:
-- @(checked index, declared index, term)@. The two lists zip exactly:
-- 'retainedIndices' selects one declared index per checked argument, in
-- checked declaration order.
argSites :: Prune -> [(CheckedIx, DeclaredIx, SupportTerm)]
argSites p =
  [ (CheckedIx ci, DeclaredIx di, w)
  | ((ci, di), (_, w)) <- zip (zip [0 ..] (retainedIndices p)) (unitArgs (pruneChecked p))
  ]

-- | All rule occurrences across the checked arguments:
-- @(checked arg index, declared arg index, position, occurrence)@.
ruleSites :: Prune -> [(CheckedIx, DeclaredIx, Position, SupportTerm)]
ruleSites p =
  [ (ci, di, pos, t)
  | (ci, di, w) <- argSites p
  , (pos, t@SRule{}) <- occurrences w
  ]

-- | All leaf-reference occurrences across the checked arguments.
leafSites :: Prune -> [(CheckedIx, DeclaredIx, Position, LeafId)]
leafSites p =
  [ (ci, di, pos, l)
  | (ci, di, w) <- argSites p
  , (pos, SLeaf l) <- occurrences w
  ]

-- | The checked unit's attacks with both indices — the attack counterpart of
-- 'argSites', bridged by 'retainedAttackIndices'. Only retained attacks are
-- sites: a pruned attack never reaches the typed-attack stage.
attackSites :: Prune -> [(CheckedIx, DeclaredIx, Attack)]
attackSites p =
  [ (CheckedIx ci, DeclaredIx di, k)
  | ((ci, di), k) <- zip (zip [0 ..] (retainedAttackIndices p)) (unitAttacks (pruneChecked p))
  ]

ruleOf :: Unit -> RuleId -> Maybe Rule
ruleOf u rn = find ((== rn) . ruleId) (unitRules u)

-- | A declared leaf whose proposition is ≢ the wanted one (the swap target
-- for premise\/discharge mismatch mutations). Callers pass the /checked/ unit:
-- a swap target drawn from quarantined Γ would make the mutated
-- argument use a quarantined leaf, pruning it out of the checked unit — the
-- mutation would vanish instead of manifesting.
inequivLeaf :: Unit -> Prop -> Maybe LeafId
inequivLeaf u p = fst <$> find (not . equiv p . snd) (unitLeaves u)
