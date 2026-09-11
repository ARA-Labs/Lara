-- | Stage four of the multi-artifact map: merge the qualified members into one
-- unit, complete the cross-member attacks, and run the __ordinary__ checker on
-- the result.
--
-- == Position in the pipeline
--
-- @
-- .laramap bytes -> decode  ("Lara.Map.Wire")
--                -> load and recheck each member  ("Lara.Map.Load")
--                -> qualify each member's local identities  ("Lara.Map.Qualify")
--                -> merge \/ saturate \/ check \/ evaluate    <- here
--                -> composite verdict  (\@Lara.Map.Driver\@, issue #303)
-- @
--
-- == Nothing is asserted; everything is checked
--
-- This module builds a 'Lara.AST.Unit' and hands it to 'Lara.Check.checkUnit'.
-- It does not construct a 'Lara.Compile.CheckedProgram', does not extend the
-- checker, and does not carry any member's acceptance forward as a licence for
-- the linked program. The consequence is the point: __a map cannot accept
-- anything a hand-written equivalent unit would not__, and in particular the
-- cross-member attacks the saturation generates are typed by the ordinary
-- 'Lara.Attack.checkAttack' like any other, against the same shared policy.
--
-- The generation step exists because 'Lara.Check.firstMissingConflictInfo' is an
-- __all-pairs__ scan: a link that merely concatenated two members' attack lists
-- would leave every cross-member contrary pair uncovered, and the linked unit
-- would be rejected for a missing conflict. Saturation is what makes the
-- all-pairs condition satisfiable; the checker is still what decides it.
--
-- That claim is exact against 'Lara.Check.checkUnit' and __not__ against
-- 'Lara.Driver.Internal.runCheck'. The solo @.lara@ door runs the §4.3 prune
-- first ('Lara.Driver.Internal.prune'), which is the only thing in the codebase
-- that reads @unitGroups@ or @unitGroupMode@: it quarantines arguments built on
-- a conflicted duplicate-report group, or rejects the program as R9 when the
-- policy escalates. 'checkUnit' reads neither field. So the linked unit carries
-- every member's groups __unaudited__, and @ssGroupMode@ is compared across
-- members and then used for nothing.
--
-- That is sound today for one reason, and it is a property of the /loader/, not
-- of this module: "Lara.Map.Load" refuses any member whose admission or
-- group-pruning audit is nonempty ('Lara.Map.Types.MRUnsupportedAdmission'), so
-- every member that reaches here has consistent groups and the prune would be a
-- no-op. __A later relaxation of that load gate would silently break this
-- module__ — a map could then accept a unit the solo door would R9-reject —
-- which is why the dependency is written down here rather than left to be
-- rediscovered.
--
-- == The merge, and the handles it must not lose
--
-- 'Lara.Check.firstDuplicate' rejects a unit that declares one support term
-- twice, so structurally identical terms coming from different members are
-- __merged__ into one linked argument rather than rejected. Every original
-- @(alias, local 'ArgId')@ handle is retained in the node table pointing at that
-- one index, so a report can always name every member that independently
-- produced an argument.
--
-- Because "Lara.Map.Qualify" renames every leaf occurrence by its member's
-- alias, a term that mentions a leaf can only collide with a term of the /same/
-- member — and a member's own unit has already been through
-- 'Lara.Check.firstDuplicate'. The merge therefore fires only on __leaf-free__
-- terms (an instance of a premise-less rule). Neither shipped policy
-- (@empirical-v1@, @agreement-v1@) has one. The map fixture
-- @test\/fixtures\/map\/merge\/@ is written under a policy that does
-- (@convention-v1@), so the merge, the endpoint re-pointing it forces
-- ('renameTable') and the co-owned saturation pair below are exercised through
-- 'linkMap' and compared across both drivers, as well as directly on
-- synthesized terms (issue #316). It would be implemented regardless: the
-- alternative is a linked unit whose well-formedness silently depends on a
-- property of the policy.
--
-- The merge is also the one thing that makes \"cross-member only\" less than
-- literal. Once a term co-owned by members A and B is one linked argument, a
-- pair whose source and target are both /also/ owned by A alone can satisfy
-- 'crossMember' — from A's point of view a within-member attack it never
-- declared. That is forced rather than wrong: the two members' terms are now one
-- node, so covering B's copy necessarily covers A's. The merge fixture reaches
-- exactly this case: its co-owned argument against the critic's own objection
-- generates the rebuttals the critic already declared, and the attack dedupe
-- folds them together.
--
-- == Determinism
--
-- Two runs of one map, and two implementations of it, must produce the same
-- bytes. Every list this module builds therefore has a stated order, and none of
-- them is sorted after the fact:
--
--   * linked arguments — member order, then that member's declaration order,
--     first occurrence winning a merge;
--   * nodes — member order, then that member's declaration order;
--   * attacks — every member's declared attacks first (member order, then
--     declaration order), then the generated ones in ascending
--     @(source index, target index)@;
--   * labels — ascending index, covering exactly @0 .. n-1@;
--   * edges — ascending lexicographic @(source, target)@, exactly as
--     'Lara.Driver.buildAccept' emits them;
--   * statuses — member order, then that member's own claim declaration order.
module Lara.Map.Link
  ( -- * Linking a loaded map
    linkMap
    -- * The linked map
    -- | 'LinkedMap' is opaque: the constructor is the promise that
    -- 'Lara.Check.checkUnit' accepted the unit these projections were read off.
  , LinkedMap
  , lmUnit
  , lmNodes
  , lmLabels
  , lmEdges
  , lmStatuses
  , lmGenerated
    -- * The structural merge, exposed for direct testing
    -- | Exported so that the merge and the endpoint re-pointing it forces can be
    -- exercised shape by shape on synthesized members. Through 'linkMap' they
    -- are reached only by a leaf-free term (see the module header).
  , LinkedArg (..)
  , mergeArguments
  , renameTable
  , repoint
    -- * The structural failure arms, exposed for direct testing
    -- | Each of these refuses a condition 'linkMap' cannot reach: after
    -- qualification no two members share a leaf or argument identity, and the
    -- loader has already compared every member to one contract. That makes them a missing __tripwire__ rather than a
    -- hidden bug — and a tripwire nothing can break is one nothing would
    -- notice the day the saturation and the attack checker come apart, which
    -- is exactly when the decision record says an anchor should exist. Driving
    -- them needs synthesized inputs: 'linkedLeaves' and 'linkedArguments' take
    -- already-exported types, and 'sharedSections' takes 'CheckedMember's,
    -- which "Lara.Map.Load.Internal" exists to let a test build.
  , sharedSections
  , SharedSections (..)
  , linkedLeaves
  , linkedArguments
  ) where

import Data.List.NonEmpty (NonEmpty ((:|)))
-- Qualified for the reason "Lara.Map.Driver" gives: a plain import of
-- @foldl'@ is required on GHC 9.6 and redundant on 9.10, and a qualified one is
-- clean on both.
import qualified Data.List as List
import Data.Maybe (fromMaybe)

import Lara.AST
  ( ArgId
  , Attack (..)
  , Contrary
  , Exception
  , GroupConflictMode
  , Label
  , LeafId
  , Rule
  , RuleId
  , Status
  , SupportTerm (..)
  , TheoryDigest
  , Unit (..)
  )
import Lara.Attack (contraryMatchB)
import Lara.Check (CheckedUnit, checkUnit, cuNodes, cuProgram)
import Lara.Compile (conflictAttackableB)
import Lara.Diagnostics (rejectionOf)
import Lara.Driver (buildCertOk, buildGamma)
import Lara.Grounded (AF (..), completeClaimFor, labelC, statusC)
import Lara.Map.Load
  ( CheckedMember
  , CheckedMembers
  , checkedMembers
  , cmAlias
  , cmClaims
  , cmUnit
  )
import Lara.Map.Qualify
  ( LocalArgId
  , QualifiedArg (..)
  , QualifiedMember (..)
  , localArgId
  , qualifiedArgId
  , qualifyMember
  )
import Lara.Map.Types
  ( MapError (..)
  , MapNode (..)
  , MapRejectError (..)
  , MapStatus (..)
  , MemberAlias
  , NodeIndex
  , aliasText
  , mkNodeIndex
  )
import Lara.Policy (lookupRule)
import Lara.Prop (Prop)
import Lara.Runtime (runtimeAF)
import Lara.Sigma (Sigma)
import Lara.SupportTerm
  ( CertOk
  , CheckLoc (LocRoot)
  , inferSupport
  , srConclusion
  , srObligations
  )

-- ---------------------------------------------------------------------------
-- The linked map
-- ---------------------------------------------------------------------------

-- | One argument of the linked unit: the term, the identity it was given, the
-- position it occupies, and every member that declared it.
--
-- 'laOwners' is what makes the merge reportable rather than lossy. It is in
-- member order and duplicate-free, and it is nonempty by construction — a
-- linked argument exists because some member declared its term.
data LinkedArg = LinkedArg
  { laArgId :: ArgId
    -- ^ the qualified identity of the __first__ member that declared this term;
    -- the linked unit names the argument by it
  , laTerm :: SupportTerm
  , laIndex :: Int
    -- ^ the argument's position in the linked unit, which is also its node
    -- index in the compiled framework
  , laOwners :: [MemberAlias]
  }
  deriving (Eq, Show)

-- | A checked, evaluated map: the linked unit, the provenance mapping back to
-- each member's own handles, and the grounded result.
--
-- __Opaque.__ The constructor is the promise, exactly as it is for
-- 'Lara.Map.Load.CheckedMember': a 'LinkedMap' exists only where 'linkMap'
-- built a unit out of loaded members, ran 'Lara.Check.checkUnit' on it, and got
-- an acceptance. Exporting the constructor would let a caller assemble a
-- \"linked\" map around a unit nothing had checked, and the composite verdict's
-- meaning would become a convention rather than a consequence.
--
-- Note what is /not/ here: no 'Lara.Compile.CheckedProgram' and no
-- 'Lara.Check.CheckedUnit' escapes. The observers below are projections of the
-- accepted unit taken at construction time, so no consumer can re-enter the
-- checker's internals through this type.
data LinkedMap = LinkedMap
  { lmUnitField :: Unit
  , lmNodesField :: [MapNode]
  , lmLabelsField :: [(NodeIndex, Label)]
  , lmEdgesField :: [(NodeIndex, NodeIndex)]
  , lmStatusesField :: [MapStatus]
  , lmGeneratedField :: [Attack]
  }

-- | The linked unit: every member's qualified leaves, the merged arguments, the
-- transported and generated attacks, and the shared policy's own sections.
lmUnit :: LinkedMap -> Unit
lmUnit = lmUnitField

-- | The provenance mapping: one entry per @(member alias, local 'ArgId')@ that
-- any member declared, naming the linked argument index it resolved to.
--
-- In member order, then that member's own declaration order. Several entries
-- share an index exactly when the merge fired.
lmNodes :: LinkedMap -> [MapNode]
lmNodes = lmNodesField

-- | The grounded labelling of the linked framework, ascending by index and
-- covering exactly @0 .. n-1@.
lmLabels :: LinkedMap -> [(NodeIndex, Label)]
lmLabels = lmLabelsField

-- | The compiled closure edges, ascending lexicographic.
lmEdges :: LinkedMap -> [(NodeIndex, NodeIndex)]
lmEdges = lmEdgesField

-- | One map-relative status per @(member alias, claim name)@, in member order
-- and then that member's own claim declaration order.
--
-- These are the /map's/ statuses, not the members'. A claim a member proved on
-- its own can be contested or defeated here, because grounded status is not
-- preserved when a framework is extended. That non-preservation is the whole
-- reason a map is worth computing; it is exhibited by a concrete accepted
-- witness in @lean\/Lara\/Map\/Link.lean@ rather than assumed away, and there is
-- deliberately no monotonicity theorem anywhere in this development.
lmStatuses :: LinkedMap -> [MapStatus]
lmStatuses = lmStatusesField

-- | The attacks the __cross-member saturation__ generated, in the order it
-- generated them and __before__ deduplication against the transported ones.
--
-- Almost always that means \"the attacks no member declared\", because a
-- generated attack crosses a member boundary and a declared one does not. The
-- exception is the merge: when one term is owned by two members, a pair the
-- saturation generates for can coincide with an attack one of them declared, and
-- that attack appears both here and in the transported list. @'unitAttacks' .
-- 'lmUnit'@ is the deduplicated union and carries it once.
lmGenerated :: LinkedMap -> [Attack]
lmGenerated = lmGeneratedField

-- ---------------------------------------------------------------------------
-- Linking
-- ---------------------------------------------------------------------------

-- | Merge a loaded map's members into one unit, complete its cross-member
-- attacks, check it, and evaluate it.
--
-- The stages, and only the first failure is reported:
--
--   1. the shared policy sections of the members' units are compared —
--      'MRLinkBoundary'. This cannot fire (see 'sharedSections');
--   2. every member is qualified and the qualified leaf contexts are
--      concatenated; a repeated leaf identity is 'MRLinkBoundary'. This cannot
--      fire either (see 'linkedLeaves');
--   3. the arguments are merged, the members' own attacks are transported, and
--      the cross-member attacks are generated;
--   4. 'Lara.Check.checkUnit' runs on the linked unit — a rejection is
--      'MRLinkRejected', carrying the ordinary wire rejection class through
--      'Lara.Diagnostics.rejectionOf', so a map names a rejection exactly as a
--      solo verdict does;
--   5. the accepted unit is evaluated: grounded labels, closure edges, and one
--      four-state status per member claim.
--
-- Stages 1 and 2 are guards whose failure is unreachable given what
-- "Lara.Map.Load" has already established. They are checked rather than assumed
-- because the alternative is a partial pattern, and because a loader or
-- elaborator change that broke either invariant should fail loudly here instead
-- of producing a linked unit built out of one member's signature and another's
-- rules. This is the same reasoning
-- @Lara.Map.Load.elaboratedContractFailure@ records for its own unreachable
-- field.
linkMap :: CheckedMembers -> Either MapError LinkedMap
linkMap loaded = do
  -- No empty-map arm. 'Lara.Map.Load.checkedMembers' is a 'NonEmpty', which is
  -- where "a map declares at least one member" is now decided; this stage used
  -- to re-decide it and could only ever take the accepting branch. The Lean
  -- driver's counterpart raised the same condition as an @Except String@ and
  -- exited 2 where this exited 1 — a divergence unobservable because both
  -- decoders refuse an empty map first, and now unrepresentable on this side.
  let firstMember :| laterMembers = checkedMembers loaded
      members = firstMember : laterMembers
  shared <- sharedSections firstMember laterMembers
  let qualified = [qualifyMember (cmAlias member) (cmUnit member) | member <- members]
  leaves <- linkedLeaves qualified
  let (linkedArgs, handles) = mergeArguments qualified
  nodes <- traverse toNode handles
  args <- linkedArguments linkedArgs
  let pI = lookupRule (ssRules shared)
      gamma = buildGamma leaves
      certOk = buildCertOk (ssTheories shared)
      renames = renameTable linkedArgs qualified
      transported = [repoint renames attack | member <- qualified, attack <- qmAttacks member]
      generated = crossMemberAttacks shared (conclusionCache pI gamma certOk linkedArgs)
      unit =
        Unit
          { unitSigma = ssSigma shared
          , unitRules = ssRules shared
          , unitContraries = ssContraries shared
          , unitExceptions = ssExceptions shared
          , unitTheories = ssTheories shared
          , unitLeaves = leaves
          , unitArgs = args
          , unitAttacks = dedupe (transported ++ generated)
          , -- The members' own @status@ declarations, transported. The linked
            -- unit carries them so it is a faithful unit rather than a
            -- convenience object, but nothing here reads them: a map's statuses
            -- are keyed by @(member alias, claim name)@ and come from
            -- 'cmClaims', which a 'Unit' has lost.
            unitQueries = dedupe (concatMap qmQueries qualified)
          , unitGroups = concatMap qmGroups qualified
          , unitGroupMode = ssGroupMode shared
          }
  accepted <- case checkUnit gamma certOk unit of
    Left unitError -> Left (MapReject (MRLinkRejected (rejectionOf unitError)))
    Right checked -> Right checked
  evaluate members unit nodes generated accepted
  where
    -- 'mnArg' is the verdict's __reporting__ handle: the name the member's own
    -- author wrote. The 'LocalArgId' wrapper is unwrapped here, at the wire
    -- boundary, so that everything upstream of it is unable to supply the
    -- qualified key by mistake — 'MapNode' is a wire type and cannot carry a
    -- map-only wrapper.
    toNode (alias, local, position) = do
      index <- requireIndex position
      pure MapNode{mnAlias = alias, mnArg = localArgId local, mnIndex = index}

-- | The one place a structural link failure is spelled.
linkBoundary :: String -> MapError
linkBoundary = MapReject . MRLinkBoundary

-- ---------------------------------------------------------------------------
-- The shared policy sections
-- ---------------------------------------------------------------------------

-- | The sections of a member's 'Lara.AST.Unit' that come from the __shared
-- policy__ rather than from the member's own text. The linked unit carries
-- exactly one copy of each.
data SharedSections = SharedSections
  { ssSigma :: Sigma
  , ssRules :: [Rule]
  , ssContraries :: [Contrary]
  , ssExceptions :: [Exception]
  , ssTheories :: [(TheoryDigest, [Prop])]
  , ssGroupMode :: GroupConflictMode
  }

-- | Read the shared sections off the first member and assert every other member
-- agrees, naming the first field that does not.
--
-- __This cannot fire__, and the reason is worth stating rather than trusting:
-- "Lara.Map.Load" compares every member to the /manifest's/ policy on
-- 'Lara.Map.Types.CFPolicyStructure' (the whole parsed 'Lara.AST.Policy', by
-- @==@), on 'Lara.Map.Types.CFSignature' and on 'Lara.Map.Types.CFTheories', so
-- any two members that reach this function agree with each other on all six
-- fields by transitivity. What is checked here is that consequence, on the
-- objects this module actually merges.
--
-- The comparison is against the __first member__ rather than against the
-- manifest because 'Lara.Map.Load.CheckedMembers' does not carry the contract
-- policy. No member is privileged by that choice: the check is an equality over
-- the whole list either way, and it names both aliases when it reports.
--
-- The first member is a separate argument rather than the head of a list so that
-- there is __no empty case to answer__. A list argument would need an arm for
-- @[]@, which could only repeat the diagnostic 'linkMap' has already issued —
-- two spellings of one condition, and a second place to keep them in step.
sharedSections :: CheckedMember -> [CheckedMember] -> Either MapError SharedSections
sharedSections first rest = List.foldl' step (Right shared) rest
  where
    unit0 = cmUnit first
    shared =
      SharedSections
        { ssSigma = unitSigma unit0
        , ssRules = unitRules unit0
        , ssContraries = unitContraries unit0
        , ssExceptions = unitExceptions unit0
        , ssTheories = unitTheories unit0
        , ssGroupMode = unitGroupMode unit0
        }
    step acc member = do
      sections <- acc
      case disagreement sections (cmUnit member) of
        Just field ->
          Left . linkBoundary $
            "members "
              ++ aliasText (cmAlias first)
              ++ " and "
              ++ aliasText (cmAlias member)
              ++ " disagree on the shared policy's "
              ++ field
        Nothing -> Right sections

    disagreement sections unit
      | unitSigma unit /= ssSigma sections = Just "signature"
      | unitRules unit /= ssRules sections = Just "rules"
      | unitContraries unit /= ssContraries sections = Just "contraries"
      | unitExceptions unit /= ssExceptions sections = Just "exceptions"
      | unitTheories unit /= ssTheories sections = Just "theories"
      | unitGroupMode unit /= ssGroupMode sections = Just "duplicate-report mode"
      | otherwise = Nothing

-- ---------------------------------------------------------------------------
-- The linked leaf context
-- ---------------------------------------------------------------------------

-- | Concatenate the members' qualified leaf contexts, in member order, refusing
-- a repeated identity.
--
-- __This cannot fire__, and there are exactly three ways it could:
--
--   * two members share an alias — the manifest decoder refuses that, and
--     "Lara.Map.Types"'s D10 note records that it owns the rule outright;
--   * 'Lara.Map.Types.qualifiedKey' is not injective — its length framing is
--     what makes it so, with 'Lara.Map.Types.parseQualifiedKey' the operational
--     witness and @qualifiedKey_inj@ in @lean\/Lara\/Map\/Qualify.lean@ the
--     mechanized one;
--   * __one member declares one 'LeafId' twice__, which qualification maps to a
--     collision with itself rather than with a peer. 'Lara.Elaborate.prepareSource'
--     refuses that source as @DuplicateSourceLeafId@ before it can become a
--     member, and every map member reaches this module through that call. (The
--     wire decoder is /not/ a second guard here: its @leaves@ decoder scans no
--     duplicates, and no map member arrives through it.)
--
-- The check is here because 'Lara.Driver.buildGamma' is first-wins: a silent
-- collision would let one member's leaf shadow another's, and every argument
-- built on the shadowed leaf would then be checked against a proposition its
-- author never wrote.
linkedLeaves :: [QualifiedMember] -> Either MapError [(LeafId, Prop)]
linkedLeaves qualified = go [] (concatMap qmLeaves qualified)
  where
    go seen [] = Right (reverse seen)
    go seen (entry@(l, _) : rest)
      | l `elem` map fst seen =
          Left (linkBoundary ("two members declare the leaf identity " ++ show l))
      | otherwise = go (entry : seen) rest

-- | The linked unit's argument list, refusing a repeated identity.
--
-- __This discharges the argument-id half of R14__, which 'Lara.Check.checkUnit'
-- states as an input contract and does not recheck: \"a caller that forges a
-- 'Unit' bypassing the decoder owns this precondition\". 'linkMap' is exactly
-- such a caller — no 'Lara.Wire.decodeUnit' runs on a linked unit — so the
-- obligation is this module's.
--
-- __It cannot fire__, for the same two reasons 'linkedLeaves' cannot: aliases
-- are unique (the manifest decoder owns that) and 'Lara.Map.Types.qualifiedKey'
-- is injective, so two members' arguments cannot share an identity; and within
-- one member the identities are unique because 'Lara.Elaborate.prepareSource'
-- refuses a repeated @arg@ id as @DuplicateArgId@.
--
-- It is checked because a violation would be __silent and maximally
-- confusing__, not because it is expected. 'Lara.Check.firstDuplicate' would not
-- catch it: it is @:: ['SupportTerm']@ and compares /terms/, so two arguments
-- sharing an id but not a term pass it. What would then happen is worse than a
-- rejection — 'Lara.Check.resolveAttacks' resolves an endpoint by @lookup@,
-- which is first-wins, so one member's declared attacks would be quietly
-- retargeted onto another member's argument and the map would report a verdict
-- about a graph nobody wrote.
linkedArguments :: [LinkedArg] -> Either MapError [(ArgId, SupportTerm)]
linkedArguments = go []
  where
    go seen [] = Right (reverse seen)
    go seen (arg : rest)
      | laArgId arg `elem` map fst seen =
          Left
            ( linkBoundary
                ("two linked arguments share the identity " ++ show (laArgId arg))
            )
      | otherwise = go ((laArgId arg, laTerm arg) : seen) rest

-- ---------------------------------------------------------------------------
-- The structural merge
-- ---------------------------------------------------------------------------

-- | Merge the members' arguments into the linked argument list, and build the
-- provenance handles beside it.
--
-- Two arguments become one linked argument exactly when their terms are
-- structurally equal, which is the identity 'Lara.Check.firstDuplicate' uses to
-- reject a duplicate. The __first__ member to declare a term fixes the linked
-- argument's identity and position; a later member's declaration adds an owner
-- and a handle and nothing else.
--
-- Both results are in member order, then that member's own declaration order.
-- The handle list has exactly one entry per @(member, declared argument)@ pair,
-- so it is a total map from every original handle to a linked position — a
-- member never loses its own name for its own argument, whether or not the merge
-- fired.
--
-- The handles carry a plain 'Int' rather than a
-- 'Lara.Map.Types.NodeIndex' so that this function is total and has no error
-- channel; 'linkMap' converts each through 'Lara.Map.Types.mkNodeIndex', which
-- is where a fabricated index would otherwise have to be invented.
--
-- Exported so the merge can be exercised directly on synthesized terms, where
-- each shape can be stated on its own. Through 'linkMap' it is reached only by
-- a leaf-free term (see the module header), which the map fixture
-- @test\/fixtures\/map\/merge\/@ supplies.
mergeArguments :: [QualifiedMember] -> ([LinkedArg], [(MemberAlias, LocalArgId, Int)])
mergeArguments qualified = (linkedArgs, handles)
  where
    declared = [(qmAlias member, arg) | member <- qualified, arg <- qmArgs member]

    linkedArgs =
      [ LinkedArg
          { laArgId = qualifiedArgId (qaQualified arg)
          , laTerm = qaTerm arg
          , laIndex = position
          , laOwners = ownersOf (qaTerm arg)
          }
      | (position, (_, arg)) <- zip [0 ..] (firstOccurrences [] declared)
      ]

    -- The distinct terms, in first-declaration order. 'SupportTerm' has
    -- structural 'Eq' and no 'Ord', so the scan is a linear membership test
    -- rather than a map lookup; a map's argument count is bounded by what its
    -- members declared.
    firstOccurrences _ [] = []
    firstOccurrences seen (entry@(_, arg) : rest)
      | qaTerm arg `elem` seen = firstOccurrences seen rest
      | otherwise = entry : firstOccurrences (qaTerm arg : seen) rest

    ownersOf term = dedupe [alias | (alias, arg) <- declared, qaTerm arg == term]

    -- @take 1@ is the first (and only) match. It is never empty: every declared
    -- argument's term either is a first occurrence, and so has its own linked
    -- argument, or equals an earlier one, and so has that one's. The handle list
    -- is therefore the same length as @declared@ — which
    -- @prop_nodesAreTotalProvenance@ asserts on a real map rather than leaving
    -- to this comment.
    handles =
      [ (alias, qaLocal arg, position)
      | (alias, arg) <- declared
      , position <- take 1 [laIndex linked | linked <- linkedArgs, laTerm linked == qaTerm arg]
      ]

-- | The rename every member-local qualified argument identity undergoes when the
-- merge folds its term onto an earlier member's argument.
--
-- Identity everywhere the merge did not fire, which is everywhere under the
-- shipped policies: neither has a premise-less rule (see the module header).
renameTable :: [LinkedArg] -> [QualifiedMember] -> [(ArgId, ArgId)]
renameTable linkedArgs qualified =
  [ (qualifiedArgId (qaQualified arg), canonical)
  | member <- qualified
  , arg <- qmArgs member
  , canonical <- take 1 [laArgId linked | linked <- linkedArgs, laTerm linked == qaTerm arg]
  ]

-- | Re-point an attack's endpoints at the linked arguments their terms became,
-- keeping its kind and its position path.
--
-- An endpoint absent from the table is left alone. __The fallback is safe only
-- because it is unreachable__, and that is worth stating precisely, because
-- nothing downstream would catch it: 'renameTable' has a key for every argument
-- every member declared, so no endpoint of a transported attack can miss.
--
-- Were one to miss, the checker would /not/ report it.
-- 'Lara.Check.resolveAttacks' resolves endpoints with @mapMaybe@ over @lookup@,
-- so an attack naming an undeclared argument is __dropped before__
-- 'Lara.Check.checkAttacks' ever sees it — 'Lara.Check.checkUnit''s own contract
-- note says so. The R1 arm in 'Lara.Check.checkAttacks' fires on a /resolved/
-- attack whose term is not a declared argument, which is a different condition
-- and not this one. So the totality here rests on 'renameTable', not on a
-- downstream diagnosis.
repoint :: [(ArgId, ArgId)] -> Attack -> Attack
repoint table attack = case attack of
  Rebut source target -> Rebut (rename source) (rename target)
  Undercut source target position -> Undercut (rename source) (rename target) position
  Undermine source target position -> Undermine (rename source) (rename target) position
  where
    rename a = fromMaybe a (lookup a table)

-- ---------------------------------------------------------------------------
-- Cross-member saturation
-- ---------------------------------------------------------------------------

-- | One linked argument that infers a conclusion, with what the saturation needs
-- to decide a pair.
data ConclusionEntry = ConclusionEntry
  { ceArg :: LinkedArg
  , ceConclusion :: Prop
  , ceAttackable :: Bool
  }

-- | The conclusions of the linked arguments that are __complete checked
-- support__ under the linked environment, in linked-argument order.
--
-- A term that fails to infer, or that retains an open critical-question
-- obligation, contributes no conclusion and therefore no cross-member attack.
-- That is not leniency: 'Lara.Check.checkUnit' runs afterwards and rejects the
-- linked unit for exactly those terms, so the only effect of skipping them here
-- is that the saturation does not emit an attack whose endpoint the checker is
-- about to refuse. This mirrors @conclusionOf@ in
-- @lean\/Lara\/Context\/Fragment.lean@, whose cache is total exactly where
-- acceptance is possible.
conclusionCache
  :: (RuleId -> Maybe Rule)
  -> (LeafId -> Maybe Prop)
  -> CertOk
  -> [LinkedArg]
  -> [ConclusionEntry]
conclusionCache pI gamma certOk args =
  [ ConclusionEntry
      { ceArg = arg
      , ceConclusion = srConclusion result
      , ceAttackable = conflictAttackableB pI (laTerm arg)
      }
  | arg <- args
  , Right result <- [inferSupport pI gamma certOk LocRoot (laTerm arg)]
  , null (srObligations result)
  ]

-- | Every attack a cross-member conflict forces, in ascending
-- @(source position, target position)@.
--
-- The rule is the one @crossAttsFrom@ uses in
-- @lean\/Lara\/Context\/Fragment.lean@: for an ordered pair of complete checked
-- arguments whose conclusions are a declared contrary instance and whose
-- __target__ can be the subject of a conflict attack, emit the attack in the
-- shape the target admits ('attackFor'). Both shapes put the attacked occurrence
-- at the target itself, so the compiled edge exists by structural containment,
-- and 'Lara.Compile.coveredB' carries it on to every declared argument that
-- contains the target — the subargument closure, applied across the member
-- boundary.
--
-- __Only cross-member pairs are generated__, and that restriction is
-- load-bearing rather than an optimisation. A same-member pair is already the
-- business of that member's own declarations: the member's solo check ran the
-- same all-pairs scan and either found the pair covered or rejected the member.
-- Emitting an extra attack for such a pair would be sound but not inert — a root
-- rebut covers every argument containing the target, where the member's own
-- undercut at a position covers less — so the map would add edges the member's
-- author never declared and the solo verdict never had.
--
-- \"Cross-member\" is 'crossMember', which reads the /owner lists/ the merge
-- built, so the phrase is exact only while the merge is inactive. Once one term
-- is co-owned, a pair whose two sides are also both owned by one member
-- satisfies it — see the module header, where the case and its justification are
-- stated in full. Reached only when the merge fires, which the shipped policies
-- never make it do; @test\/fixtures\/map\/merge\/@ does.
crossMemberAttacks :: SharedSections -> [ConclusionEntry] -> [Attack]
crossMemberAttacks shared cache =
  [ attackFor (ceArg source) (ceArg target)
  | source <- cache
  , target <- cache
  , crossMember (laOwners (ceArg source)) (laOwners (ceArg target))
  , contraryMatchB (ssContraries shared) (ceConclusion source) (ceConclusion target)
  , ceAttackable target
  ]

-- | Two linked arguments are a cross-member pair when some member declared the
-- one and a __different__ member declared the other.
--
-- With the merge inactive each owner list is a singleton and this is alias
-- inequality. With the merge active there are two further cases, and both are
-- forced by the merge rather than invented by this predicate:
--
--   * __a co-owned term against itself__ — a term owned by @{A, B}@ is a
--     cross-member pair with itself. That is exactly right: the all-pairs scan
--     quantifies over ordered self-pairs too, and two members that independently
--     produced one term have genuinely produced a conflict across the boundary
--     when its conclusion is contrary to itself.
--   * __a co-owned term against a singly-owned one__ — @{A, B}@ against @{A}@
--     satisfies this, although from @A@'s own point of view it is a within-member
--     pair @A@ never declared an attack for. It is still forced: after the merge
--     @A@'s copy and @B@'s copy of the term are one node, so an attack that
--     covers the conflict for @B@ covers it for @A@ too. Refusing to emit here
--     would leave a genuine cross-boundary conflict uncovered and the linked
--     unit would be rejected for a missing conflict.
--
-- Neither arises under the shipped policies, for the reason the module header
-- gives; @test\/fixtures\/map\/merge\/@ reaches the second. The second is the
-- one that makes \"only cross-member pairs are generated\" less than literal;
-- 'crossMemberAttacks' says so at its own site.
crossMember :: [MemberAlias] -> [MemberAlias] -> Bool
crossMember sources targets =
  or [source /= target | source <- sources, target <- targets]

-- | The attack shape a target admits: undermine a leaf at its root position,
-- rebut a rule instance (@attackFor@, @lean\/Lara\/Context\/Fragment.lean@).
attackFor :: LinkedArg -> LinkedArg -> Attack
attackFor source target = case laTerm target of
  SLeaf _ -> Undermine (laArgId source) (laArgId target) []
  SRule{} -> Rebut (laArgId source) (laArgId target)

-- | Keep the first occurrence of each element.
--
-- The generated attacks are distinct by construction: at most one per ordered
-- pair of linked arguments. A member's declared attacks carry no such guarantee
-- — __nothing upstream rejects a duplicated attack__. 'Lara.Check.firstDuplicate'
-- ranges over @[SupportTerm]@ only, and neither 'Lara.Wire.decodeUnit' nor
-- 'Lara.Elaborate.elaborate' scans the attack list for repeats, so a member may
-- legitimately declare one twice.
--
-- This is therefore defensive rather than justified by an upstream invariant,
-- and a repeat it failed to remove would be inert anyway: 'Lara.Compile.coveredB'
-- is an @any@ over the attack list, so a second copy of an attack decides no
-- edge the first did not. What it buys is a linked unit whose attack list says
-- each thing once, which is what makes @unitAttacks@ readable as a report.
dedupe :: Eq a => [a] -> [a]
dedupe = go []
  where
    go seen [] = reverse seen
    go seen (x : xs)
      | x `elem` seen = go seen xs
      | otherwise = go (x : seen) xs

-- ---------------------------------------------------------------------------
-- Evaluation
-- ---------------------------------------------------------------------------

-- | Read the grounded result off the accepted linked unit.
--
-- This is 'Lara.Driver.buildAccept''s computation without its
-- @evidence-blocked@ arm, and the omission is a consequence of the loader rather
-- than a simplification: a member whose admission or group-pruning audit is
-- nonempty is refused at load ('Lara.Map.Types.MRUnsupportedAdmission'), so no
-- query in a map can be blocked and the four-state 'Status' is total here.
evaluate
  :: [CheckedMember]
  -> Unit
  -> [MapNode]
  -> [Attack]
  -> CheckedUnit
  -> Either MapError LinkedMap
evaluate members unit nodes generated accepted = do
  labels <- traverse (\i -> (,) <$> requireIndex i <*> pure (labelC af i)) [0 .. n - 1]
  edges <-
    traverse
      (\(i, j) -> (,) <$> requireIndex i <*> requireIndex j)
      [(i, j) | i <- [0 .. n - 1], j <- [0 .. n - 1], afAttack af i j]
  pure
    LinkedMap
      { lmUnitField = unit
      , lmNodesField = nodes
      , lmLabelsField = labels
      , lmEdgesField = edges
      , lmStatusesField = statuses
      , lmGeneratedField = generated
      }
  where
    -- 'Lara.Runtime.runtimeAF' is the production builder the solo driver uses,
    -- and its verdict is byte-identical to the un-cached
    -- 'Lara.Compile.checkedAF' path; the map takes the same one so a linked unit
    -- and a hand-written equivalent unit cannot be evaluated by two different
    -- code paths.
    af = runtimeAF (cuProgram accepted)
    n = length (afArgs af)
    statuses =
      [ MapStatus
          { msAlias = cmAlias member
          , msClaim = claim
          , msAtom = atom
          , msStatus = statusOf atom
          }
      | member <- members
      , (claim, atom) <- cmClaims member
      ]
    statusOf :: Prop -> Status
    statusOf atom = statusC af (completeClaimFor (cuNodes accepted) atom)

-- | A linked-unit position as the reporting types spell it.
--
-- 'Lara.Map.Types.mkNodeIndex' refuses a negative index and every position here
-- is a list position, so the failure arm is unreachable. It is written out
-- rather than defaulted because a defaulted index would put a fabricated node
-- number in a verdict.
requireIndex :: Int -> Either MapError NodeIndex
requireIndex i = case mkNodeIndex i of
  Just index -> Right index
  Nothing -> Left (linkBoundary ("negative linked argument position " ++ show i))
