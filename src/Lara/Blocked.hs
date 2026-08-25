-- | Conservative public reporting for quarantine-affected claims (spec §4.3,
-- issue #76) — the executable counterpart of @lean\/Lara\/Blocked.lean@.
--
-- __The hazard.__ §4.3 quarantine removes a leaf, every argument whose support
-- term uses it, and every attack with a removed endpoint
-- ('Lara.Driver.quarantineUnit'), and then checks the /smaller/ program.
-- Grounded semantics is non-monotonic across graph changes, so deletion does not
-- only weaken: if the quarantined leaf backed an /attacker/, its target loses a
-- defeater and can move @contested@\/@defeated@ → @justified@. Publishing the
-- smaller graph's label as the claim status therefore lets missing evidence make
-- a claim look stronger.
--
-- __The rule.__ A query is __blocked__ when one of its complete support
-- arguments is forward-reachable, along declared attack edges, from material the
-- prune removed. Blocked queries report @evidence-blocked@; their four-state
-- label survives only as a conditional diagnostic — the 'Lara.Wire.EvidenceBlocked'
-- constructor of 'Lara.Wire.PublicStatus' carries it inside
-- 'Lara.Wire.verdictStatuses'. Everything else keeps its ordinary status.
--
-- Reachability is __directed__: grounded labelling reads only a node's
-- transitive attackers, so forward reachability from the removed material is the
-- tight rule (Lean @directIn_transfer@). Blocking the whole undirected component
-- would also be sound but blocks nearly every claim in a connected program.
--
-- __Lost edges count as removed material.__ Under subargument closure one
-- declared attack can carry edges onto arguments other than its declared target
-- ('Lara.Compile.coveredB'), so dropping an attack whose endpoint was quarantined
-- can also delete an edge /between two retained arguments/. Those targets are
-- seeded too, which is exactly the Lean @edge_agree@ obligation.
--
-- __What is proved where.__ @Lara.Blocked@ (Lean) proves the metatheory over an
-- arbitrary pair of frameworks: the locality lemma, @justified_nonpromotion@
-- (a published @justified@ is justified with the quarantined material
-- reinstated), and @statusC_agree@ (an unblocked claim whose complete-support
-- set survived the prune /unchanged/ keeps the status it would have had — the
-- equal-support premise is load-bearing: a claim whose support merely shrank
-- can move, e.g. @justified@ → @gap@, without being blocked). Lean's
-- @blocking_of_blockedSeed@ then discharges the three obligations for /this/
-- construction over declared-index frameworks. Lean's
-- @production_justified_nonpromotion_of_not_blocked@ transports the compact
-- 'Lara.Driver.buildAccept' AF and computed complete support through the
-- retained-index embedding (issue #80). @test\/BlockedSpec.hs@ and the corpus
-- differential remain conformance evidence that this Haskell computation
-- mirrors those proved definitions.
--
-- __One carrier.__ Everything here reads a 'Prune' — a declared unit paired with
-- its /own/ §4.3 quarantine, mintable only by 'prune' or
-- 'pruneWithPolicySeed'. Two adjacent @Unit@
-- parameters would be swappable with no type error, and the swap fails __open__:
-- @retainedIndices checked declared@ retains everything, so the seed is empty and
-- the promotion this module exists to suppress is published.
module Lara.Blocked
  ( -- * The §4.3 prune (spec §4.3)
    groupConsistent
  , quarantinedLeaves
  , supportUsesLeaf
  , quarantineUnit
    -- * The prune carrier
  , Prune
  , prune
  , pruneWithPolicySeed
  , pruneDeclared
  , pruneChecked
  , prunePolicyLeaves
  , pruneInconsistentGroups
  , pruneRemovedLeaves
  , pruneRemovedArgs
  , pruneRemovedAttacks
    -- * The abstract closure (Lean @closureStep@ \/ @blockedSet@)
  , blockedSet
    -- * The two frameworks in one index space
  , retainedIndices
  , retainedAttackIndices
  , retainedLeafIndices
  , declaredEdge
  , retainedEdge
    -- * The driver entry points
  , blockedSeed
  , blockedQueries
  ) where

import Data.List (nub, partition)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Lara.AST
  ( ArgId
  , Attack (..)
  , DupGroup (..)
  , LeafId
  , SupportTerm (..)
  , Unit (..)
  )
import Lara.Attack (RAttack)
import Lara.Check (resolveAttacks)
import Lara.Compile (coveredB)
import Lara.Grounded (claimSupportFor)
import Lara.Prop (Prop, equiv)
import Lara.SupportTerm (CheckedNode)

-- ---------------------------------------------------------------------------
-- The §4.3 prune
-- ---------------------------------------------------------------------------

-- | A declared duplicate-report group is @≡@-consistent iff its members'
-- propositions are pairwise @≡@ (spec §4.3). Because @≡@ is transitive, this is
-- exactly "every member @≡@ the first member". Both front doors validate group
-- well-formedness before a 'Unit' reaches here (wire "Lara.Wire".@checkGroupInvariants@
-- / @.lara@ "Lara.Elaborate".@validateGroups@), so every member normally resolves;
-- as defense-in-depth an /unresolvable/ member is treated as a conflict rather
-- than silently skipped, so a dangling member can never degrade a group to a
-- vacuously-consistent singleton and evade R9. The empty/singleton cases are
-- vacuously consistent.
groupConsistent :: Unit -> DupGroup -> Bool
groupConsistent unit = groupConsistentWith (leafIndexOf (unitLeaves unit))

-- | First-declaration leaf lookup, matching the frozen raw checker's lookup
-- semantics even for an unsanctioned duplicate-key 'Unit'.
leafIndexOf :: [(LeafId, Prop)] -> Map LeafId Prop
leafIndexOf = Map.fromListWith (\_new existing -> existing)

groupConsistentWith :: Map LeafId Prop -> DupGroup -> Bool
groupConsistentWith leafIndex (DupGroup _ members) =
  case mapM (`Map.lookup` leafIndex) members of
    Nothing -> False -- a member with no Γ entry cannot be shown ≡-consistent
    Just [] -> True
    Just (p : ps) -> all (equiv p) ps

-- | The leaf ids quarantined by a @≢@ duplicate-report group (spec §4.3): every
-- member of every inconsistent group leaves @Gamma@.
quarantinedLeaves :: Unit -> [LeafId]
quarantinedLeaves = pruneRemovedLeaves . prune

-- | Whether a support term uses any of the given leaves anywhere in its tree
-- (spec §4.3 "any argument using a conflicted cell"): the principal leaf, or a
-- premise\/discharge sub-term's leaf.
supportUsesLeaf :: [LeafId] -> SupportTerm -> Bool
supportUsesLeaf = supportUsesLeafSet . Set.fromList

supportUsesLeafSet :: Set LeafId -> SupportTerm -> Bool
supportUsesLeafSet qs = go
  where
    go (SLeaf l) = Set.member l qs
    go (SRule _ _ premises discharges _ _) =
      any go premises || any (go . snd) discharges

-- | The unit the checker actually sees under §4.3 quarantine: every argument
-- that uses a quarantined leaf is removed (that support becomes unavailable;
-- its claim surfaces as @gap@ only when no complete alternative survives),
-- together with every attack whose endpoints no longer resolve, and the
-- quarantined leaves themselves leave the context. When no group conflicts,
-- this is the identity.
quarantineUnit :: Unit -> Unit
quarantineUnit = pruneChecked . prune

attackEndpoints :: Attack -> [ArgId]
attackEndpoints k = case k of
  Rebut w u -> [w, u]
  Undercut w u _ -> [w, u]
  Undermine w u _ -> [w, u]

-- ---------------------------------------------------------------------------
-- The prune carrier
-- ---------------------------------------------------------------------------

-- | A declared unit paired with its own §4.3 quarantine. The constructor is
-- hidden and the smart producers below keep the halves tied, so they can never be
-- swapped or drawn from unrelated units — the invariant every function below
-- depends on for its safety argument. The fields are positional with ordinary
-- accessor functions: exported record selectors would keep the field labels in
-- scope for record update, letting an importer rebuild the pair
-- (@p { pruneChecked = pruneDeclared p }@) without ever seeing the constructor.
data Prune = Prune
  Unit
  [LeafId]
  [DupGroup]
  [LeafId]
  [ArgId]
  (Set ArgId)
  [Attack]
  Unit
  deriving (Eq, Show)

-- | The unit as submitted.
pruneDeclared :: Prune -> Unit
pruneDeclared (Prune declared _ _ _ _ _ _ _) = declared

-- | The one-pass policy/group quarantine of the same unit — the program the
-- checker sees.
pruneChecked :: Prune -> Unit
pruneChecked (Prune _ _ _ _ _ _ _ checked) = checked

-- | Policy-quarantined leaves in declared source order.
prunePolicyLeaves :: Prune -> [LeafId]
prunePolicyLeaves (Prune _ leaves _ _ _ _ _ _) = leaves

-- | Exact inconsistent group declarations in group declaration order.
pruneInconsistentGroups :: Prune -> [DupGroup]
pruneInconsistentGroups (Prune _ _ groups _ _ _ _ _) = groups

-- | Removed leaves in leaf declaration order.
pruneRemovedLeaves :: Prune -> [LeafId]
pruneRemovedLeaves (Prune _ _ _ leaves _ _ _ _) = leaves

-- | Removed argument identifiers in argument declaration order.
pruneRemovedArgs :: Prune -> [ArgId]
pruneRemovedArgs (Prune _ _ _ _ args _ _ _) = args

-- | Removed raw attacks in attack declaration order, including multiplicity.
pruneRemovedAttacks :: Prune -> [Attack]
pruneRemovedAttacks (Prune _ _ _ _ _ _ attacks _) = attacks

-- | The group-only producer used by the frozen raw checker path.
prune :: Unit -> Prune
prune = pruneWithPolicySeed []

-- | Build the one source-boundary prune.  Policy and inconsistent-group seeds
-- are unioned before filtering, so no argument graph is ever elaborated or
-- pruned in stages.
pruneWithPolicySeed :: [LeafId] -> Unit -> Prune
pruneWithPolicySeed policySeed declared =
  let leafIndex = leafIndexOf (unitLeaves declared)
      requestedPolicySet = Set.fromList policySeed
      policyLeaves =
        [leaf | (leaf, _) <- unitLeaves declared, Set.member leaf requestedPolicySet]
      policySet = Set.fromList policyLeaves
      inconsistentGroups =
        [ (group, Set.fromList (dgMembers group))
        | group <- unitGroups declared
        , not (groupConsistentWith leafIndex group)
        ]
      removedLeafSet =
        Set.unions (policySet : [members | (_, members) <- inconsistentGroups])
      removedLeaves =
        [leaf | (leaf, _) <- unitLeaves declared, Set.member leaf removedLeafSet]
      (removedArgPairs, keptArgs) =
        partition (supportUsesLeafSet removedLeafSet . snd) (unitArgs declared)
      removedArgs = map fst removedArgPairs
      keptArgSet = Set.fromList (map fst keptArgs)
      (keptAttacks, removedAttacks) = partition (keepsAttackWith keptArgSet) (unitAttacks declared)
      checked =
        declared
          { unitLeaves =
              [entry | entry@(leaf, _) <- unitLeaves declared, Set.notMember leaf removedLeafSet]
          , unitArgs = keptArgs
          , unitAttacks = keptAttacks
          }
   in Prune
        declared
        policyLeaves
        (map fst inconsistentGroups)
        removedLeaves
        removedArgs
        keptArgSet
        removedAttacks
        checked

-- ---------------------------------------------------------------------------
-- The abstract closure
-- ---------------------------------------------------------------------------

-- | One round of forward closure, kept inside the carrier (Lean
-- @Lara.Blocked.closureStep@). Reflexive by construction, so the iteration is
-- ascending.
closureStep :: [Int] -> (Int -> Int -> Bool) -> Set Int -> Set Int
closureStep args edge blocked =
  Set.fromList
    [y | y <- args, Set.member y blocked || any (\x -> edge x y) (Set.toList blocked)]

-- | The blocked set: the bounded forward closure of @seed@ under @edge@ (Lean
-- @Lara.Blocked.blockedSet@). Lean iterates exactly @|args|@ times and proves
-- that is already a fixed point (@closure_stable@); iterating to stability here
-- reaches the same set with fewer rounds.
blockedSet :: [Int] -> (Int -> Int -> Bool) -> [Int] -> Set Int
blockedSet args edge seed = go (Set.fromList [x | x <- seed, x `elem` args])
  where
    go blocked =
      let next = closureStep args edge blocked
       in if next == blocked then blocked else go next

-- ---------------------------------------------------------------------------
-- The two frameworks in one index space
-- ---------------------------------------------------------------------------

-- | Declaration-order indices of the arguments quarantine retained. Both
-- frameworks are indexed by the __declared__ argument list, so the checked
-- framework is a sub-carrier rather than a renumbering — the same shape the Lean
-- theorems quantify over. 'Lara.Driver.quarantineUnit' filters, so the retained
-- ids keep their declared relative order and this list also maps a checked-unit
-- argument index back to its declared index.
retainedIndices :: Prune -> [Int]
retainedIndices p =
  [ i
  | (i, (argumentId, _)) <- zip [0 ..] (unitArgs declared)
  , Set.member argumentId keptArgSet
  ]
  where
    declared = pruneDeclared p
    keptArgSet = pruneKeptArgSet p

-- | The checked argument-id index built by the smart constructor.
pruneKeptArgSet :: Prune -> Set ArgId
pruneKeptArgSet (Prune _ _ _ _ _ kept _ _) = kept

-- | An attack survives quarantine exactly when both endpoints do. The one
-- carrier for that rule: 'pruneWithPolicySeed' partitions the declared attack
-- list with it and 'retainedAttackIndices' re-expresses the same partition as
-- an index list, so the two are the /same/ binding rather than two copies of
-- one line — they cannot desync.
keepsAttackWith :: Set ArgId -> Attack -> Bool
keepsAttackWith keptArgSet attack =
  all (`Set.member` keptArgSet) (attackEndpoints attack)

-- | Declaration-order indices of the attacks quarantine retained — the attack
-- counterpart of 'retainedIndices'. 'pruneWithPolicySeed' filters, so the
-- retained attacks keep their declared relative order and entry @i@ of this
-- list is the declared index of checked-unit attack @i@. Selects with
-- 'keepsAttackWith' against 'pruneKeptArgSet' — the same binding and the same
-- kept-argument set the smart constructor partitioned with, so the two cannot
-- disagree.
retainedAttackIndices :: Prune -> [Int]
retainedAttackIndices p =
  [ i
  | (i, attack) <- zip [0 ..] (unitAttacks declared)
  , keepsAttackWith keptArgSet attack
  ]
  where
    declared = pruneDeclared p
    keptArgSet = pruneKeptArgSet p

-- | Declaration-order indices of the leaves quarantine retained — the leaf
-- counterpart of 'retainedIndices' (#165). 'pruneWithPolicySeed' filters, so
-- the retained leaves keep their declared relative order and entry @i@ of this
-- list is the declared index of checked-unit leaf @i@. Selection is by
-- membership in 'pruneRemovedLeaves' rather than the smart constructor's full
-- removed-leaf set; the two differ only on ids the declared context never
-- carries (a dangling group member), which this selection never tests, so the
-- filter is the same one that built the checked leaf list.
retainedLeafIndices :: Prune -> [Int]
retainedLeafIndices p =
  [ i
  | (i, (leaf, _)) <- zip [0 ..] (unitLeaves (pruneDeclared p))
  , Set.notMember leaf removed
  ]
  where
    removed = Set.fromList (pruneRemovedLeaves p)

-- | The edge relation of a unit in declared index space: the same structural
-- subargument-closure rule the checker compiles with ('Lara.Compile.edgeB'),
-- evaluated over the declared argument terms. Purely structural — it needs no
-- leaf context, so it is defined on the declared program even though that
-- program does not type-check once its quarantined leaves leave @Gamma@.
-- An out-of-range index can only mean a broken invariant; reporting "no edge"
-- would shrink the blocked set, so the fallback asserts an edge instead (the
-- fail-closed direction, matching 'blockedQueries').
edgeWith :: [SupportTerm] -> [RAttack] -> Int -> Int -> Bool
edgeWith terms atts i j = case (indexMaybe terms i, indexMaybe terms j) of
  (Just source, Just target) -> coveredB atts source target
  _ -> True

-- | The declared attacks, resolved against the declared arguments.
declaredAttacks :: Prune -> [RAttack]
declaredAttacks p =
  resolveAttacks (unitArgs (pruneDeclared p)) (unitAttacks (pruneDeclared p))

-- | The declared (pre-quarantine) edge relation — Lean's @G@.
declaredEdge :: Prune -> Int -> Int -> Bool
declaredEdge p = edgeWith (map snd (unitArgs (pruneDeclared p))) (declaredAttacks p)

-- | The checked (post-quarantine) edge relation in declared index space —
-- Lean's @F@. It reads the retained attacks only, so an attack dropped for a
-- quarantined endpoint loses every edge it carried, including edges between two
-- retained arguments.
--
-- The retained attacks are resolved from the exact checked projection stored
-- in 'Prune'; endpoint retention is decided only once by
-- 'pruneWithPolicySeed'.  Resolution still uses declared argument terms so the
-- relation remains in declared index space.
retainedAttacks :: Prune -> [RAttack]
retainedAttacks p =
  resolveAttacks
    (unitArgs (pruneDeclared p))
    (unitAttacks (pruneChecked p))

retainedEdge :: Prune -> Int -> Int -> Bool
retainedEdge p = edgeWith (map snd (unitArgs (pruneDeclared p))) (retainedAttacks p)

-- ---------------------------------------------------------------------------
-- The driver entry points
-- ---------------------------------------------------------------------------

-- | The material the prune touched, in declared index space: every removed
-- argument, plus every retained argument that lost an incoming edge. These are
-- exactly the @hmissing@ and @hedge@ obligations of Lean @blocking_of_seed@
-- (@hargs@ holds because 'retainedIndices' selects declared indices).
blockedSeed :: Prune -> [Int]
blockedSeed p =
  [i | i <- allIdx, i `notElem` retained]
    ++ [ j
       | j <- retained
       , any (\i -> declared' i j && not (checked' i j)) retained
       ]
  where
    allIdx = [0 .. length (unitArgs (pruneDeclared p)) - 1]
    retained = retainedIndices p
    declared' = declaredEdge p
    checked' = retainedEdge p

-- | The blocked arguments: the forward closure of 'blockedSeed' under the
-- declared edge relation.
blockedArgs :: Prune -> Set Int
blockedArgs p =
  blockedSet
    [0 .. length (unitArgs (pruneDeclared p)) - 1]
    (declaredEdge p)
    (blockedSeed p)

-- | The queries whose public status is @evidence-blocked@: those with a
-- complete support argument in 'blockedArgs'. A query with /no/ complete support
-- is @gap@ and is never blocked — losing support cannot promote a claim, and
-- routing quarantined support to @gap@ is the intended §4.3 behavior.
blockedQueries :: Prune -> [CheckedNode] -> [Prop] -> [Prop]
blockedQueries p nodes queries
  -- Fast path: quarantine removed nothing, so the checked program /is/ the
  -- declared one and no status is conditional. This keeps every non-quarantining
  -- artifact — which is all of them today — at exactly its pre-#76 cost.
  | unitArgs (pruneDeclared p) == unitArgs (pruneChecked p)
  , unitAttacks (pruneDeclared p) == unitAttacks (pruneChecked p) =
      []
  | otherwise = nub [q | q <- queries, any isBlocked (claimSupportFor nodes q)]
  where
    blocked = blockedArgs p
    retained = retainedIndices p
    -- 'claimSupportFor' indices are checked-node indices; 'blocked' holds
    -- declared indices, and 'retained' is the lift between them. The lift is
    -- total today (the two lists have equal length), but if that ever drifts the
    -- fallback must be __blocked__: this module exists to fail closed, and the
    -- Lean driver makes the same choice on the analogous uncertainty.
    isBlocked k = case indexMaybe retained k of
      Just i -> Set.member i blocked
      Nothing -> True

indexMaybe :: [a] -> Int -> Maybe a
indexMaybe xs i
  | i < 0 = Nothing
  | otherwise = case drop i xs of
      (x : _) -> Just x
      [] -> Nothing
