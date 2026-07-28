-- | Compilation with subargument closure (spec §8) — the Haskell mirror of
-- @lean/Lara/Compile.lean@ over the concrete support\/attack layers.
--
-- A checked program compiles to a Dung framework whose nodes are the declared
-- complete arguments and whose edges are the checker-built closure edges
-- ('edgeB', Lean @edgeB@): an edge @i → j@ exists iff some declared attack is
-- sourced at argument @i@ and its attacked occurrence is structurally contained
-- in argument @j@ (ASPIC+ subargument closure, 'coveredB' \/ 'containsB').
--
-- __Edges are unlabelled__ (hard constraint): the attack reason is consumed
-- when the edge is built and never retained on the AF. 'checkedAF' materialises
-- the framework by plugging 'edgeB' into the "Lara.Grounded" fixpoint interface;
-- there is no @Compile.Faithful@ oracle (a prior Lean commit eliminated it — the
-- decider /is/ the edge relation).
module Lara.Compile
  ( -- * Structural occurrence containment (Lean @containsB@)
    containsB
  , attackClosureB
    -- * Conflict attackability and declared-edge coverage
  , conflictAttackableB
  , coveredB
    -- * Checked programs and the compiled AF
    -- | 'CheckedProgram' is opaque: the constructor is hidden so a \"checked\"
    -- program cannot be forged; see "Lara.Compile.Internal". Read via 'cpArgs'
    -- \/ 'cpAtts'.
  , CheckedProgram
  , cpArgs
  , cpAtts
  , edgeB
  , checkedAF
  ) where

import Lara.AST
import Lara.Attack (RAttack (..), rSource, subterm)
import Lara.Compile.Internal (CheckedProgram (..))
import Lara.Grounded (AF (..))

-- ---------------------------------------------------------------------------
-- Structural occurrence containment (Lean @containsB@)
-- ---------------------------------------------------------------------------

-- | Does @t@ occur structurally in @v@? A total scan over @v@ and its
-- premise\/discharge subterms, self included (Lean @containsB@).
containsB :: SupportTerm -> SupportTerm -> Bool
containsB v t = v == t || sub
  where
    sub = case v of
      SLeaf _ -> False
      SRule _ _ ws d _ _ ->
        any (`containsB` t) ws || any (\(_, w) -> containsB w t) d

-- | Does the attacked occurrence of @k@ occur in @target@? (Lean
-- @attackClosureB@): the whole target term for a rebut, the subterm at the
-- attack's position for an undercut\/undermine (@Nothing@ off range gives
-- 'False').
attackClosureB :: RAttack -> SupportTerm -> Bool
attackClosureB k target = case k of
  RRebut _ u -> containsB target u
  RUndercut _ u pos -> occ u pos
  RUndermine _ u pos -> occ u pos
  where
    occ u pos = case subterm u pos of
      Just t -> containsB target t
      Nothing -> False

-- ---------------------------------------------------------------------------
-- Conflict attackability and declared-edge coverage
-- ---------------------------------------------------------------------------

-- | A support term can be the target of a conflict attack exactly when it is a
-- leaf or its root rule is known defeasible (Lean @conflictAttackableB@).
conflictAttackableB :: (RuleId -> Maybe Rule) -> SupportTerm -> Bool
conflictAttackableB pI target = case target of
  SLeaf _ -> True
  SRule rn _ _ _ _ _ -> case pI rn of
    Just r -> ruleMode r == Defeasible
    Nothing -> False

-- | A declared attack covers a compiled edge when it has the requested source
-- and its attacked occurrence is contained in the requested target (Lean
-- @coveredB@). One attack can cover both its direct target and any declared
-- wrappers containing that occurrence.
coveredB :: [RAttack] -> SupportTerm -> SupportTerm -> Bool
coveredB atts source target =
  any (\k -> rSource k == source && attackClosureB k target) atts

-- ---------------------------------------------------------------------------
-- Checked programs and the compiled AF
-- ---------------------------------------------------------------------------

-- | The checked-program edge decider (Lean @edgeB@): out-of-range on either side
-- is no edge; in range it scans the declared attacks for one sourced at
-- argument @i@ whose attacked occurrence is contained in argument @j@.
edgeB :: CheckedProgram -> Int -> Int -> Bool
edgeB p i j = case (indexMaybe (cpArgs p) i, indexMaybe (cpArgs p) j) of
  (Just source, Just target) -> coveredB (cpAtts p) source target
  _ -> False

-- | The compiled AF built from the checker's own edge decider — the oracle-free
-- 'AF' whose 'afAttack' is 'edgeB' (Lean @checkedAF@).
checkedAF :: CheckedProgram -> AF
checkedAF p =
  AF
    { afArgs = [0 .. length (cpArgs p) - 1]
    , afAttack = edgeB p
    }

indexMaybe :: [a] -> Int -> Maybe a
indexMaybe xs i
  | i < 0 = Nothing
  | otherwise = case drop i xs of
      (x : _) -> Just x
      [] -> Nothing
