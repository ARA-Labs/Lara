-- | Navigation and rewriting helpers shared by the site enumerators (#125,
-- split out of "Lara.Mutate.Sites" alongside the certificate family; see
-- @docs\/mutate-module-ownership-decision.md@).
--
-- These were private to "Lara.Mutate.Sites" before the split and stay
-- library-internal: the module is an @other-module@, and its only consumers are
-- "Lara.Mutate.Sites" and "Lara.Mutate.Sites.Cert".
--
-- Nothing here inspects an operator or an 'Lara.Mutate.Expected' — these are
-- purely structural. The load-bearing ordering invariant lives with the
-- enumerators that consume them: 'occurrences' fixes a deterministic traversal
-- order, and 'ruleSites' \/ 'leafSites' preserve it, so a change to the
-- traversal here moves committed corpus bytes.
module Lara.Mutate.Sites.Nav
  ( occurrences
  , rewriteAt
  , rewriteArg
  , ruleSites
  , leafSites
  , ruleOf
  , inequivLeaf
  ) where

import Data.List (find)

import Lara.AST
import Lara.Prop (Prop (..), equiv)

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
rewriteArg :: Int -> (SupportTerm -> SupportTerm) -> Unit -> Unit
rewriteArg ix f u =
  u
    { unitArgs =
        [ (aid, if j == ix then f t else t)
        | (j, (aid, t)) <- zip [0 ..] (unitArgs u)
        ]
    }

-- | All rule occurrences across the declared arguments:
-- @(arg index, position, occurrence)@.
ruleSites :: Unit -> [(Int, Position, SupportTerm)]
ruleSites u =
  [ (ix, pos, t)
  | (ix, (_, w)) <- zip [0 ..] (unitArgs u)
  , (pos, t@SRule{}) <- occurrences w
  ]

-- | All leaf-reference occurrences across the declared arguments.
leafSites :: Unit -> [(Int, Position, LeafId)]
leafSites u =
  [ (ix, pos, l)
  | (ix, (_, w)) <- zip [0 ..] (unitArgs u)
  , (pos, SLeaf l) <- occurrences w
  ]

ruleOf :: Unit -> RuleId -> Maybe Rule
ruleOf u rn = find ((== rn) . ruleId) (unitRules u)

-- | A declared leaf whose proposition is ≢ the wanted one (the swap target
-- for premise\/discharge mismatch mutations).
inequivLeaf :: Unit -> Prop -> Maybe LeafId
inequivLeaf u p = fst <$> find (not . equiv p . snd) (unitLeaves u)
