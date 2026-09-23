-- | Stage three of the multi-artifact map: rename one member's __local
-- identities__ into the map's namespace, so that two members declaring the same
-- @e1@ cannot collide when their material is merged into one unit.
--
-- == Position in the pipeline
--
-- @
-- .laramap bytes -> decode  ("Lara.Map.Wire")
--                -> load and recheck each member  ("Lara.Map.Load")
--                -> qualify each member's local identities   <- here
--                -> merge + saturate + check  ("Lara.Map.Link")
--                -> composite verdict  (\@Lara.Map.Driver\@)
-- @
--
-- == What is a handle and what is a meaning
--
-- The whole design is one line: __handles are member-local and get qualified,
-- meanings are shared and must not be.__
--
-- [Qualified] 'LeafId', 'ArgId', 'GroupId', and every reference to them —
--   'SLeaf' occurrences anywhere inside a 'SupportTerm' (premises and discharge
--   answers alike), both endpoints of every 'Attack', and every member of a
--   'DupGroup'.
--
-- [Not qualified] 'Lara.Prop.Prop' and 'Lara.Prop.Term' symbols,
--   'Lara.AST.Pred', 'Lara.AST.FunSym', 'RuleId', 'Lara.AST.Param',
--   'QuestionId', 'Lara.AST.ObligationId', certificate premise positions, and
--   'Lara.AST.TheoryDigest'.
--
-- The second list is not an oversight. Two members formalizing the same
-- proposition must land on the /same/ atom, because that is the only way a
-- cross-member conflict can be detected at all: 'Lara.Map.Link''s saturation
-- fires exactly where two members' conclusions form a declared contrary
-- instance. Qualifying a predicate symbol would make every member's vocabulary
-- private and every map trivially conflict-free — the composite verdict would
-- then say nothing. The same argument applies to rule identifiers (the shared
-- policy names them), to question identifiers (a discharge answers the
-- /policy's/ question, not the member's), and to a certificate's premise
-- positions (they index the rule's premise list).
--
-- == The renaming is injective, and separately so per member
--
-- Every local name is renamed to @'qualifiedKey' ('qualifyId' alias local)@ —
-- the length-framed identity form of "Lara.Map.Types", @7:paper_a2:e1@. Two
-- properties matter and both come from that framing:
--
--   * within one member the rename is __injective__, so a member cannot lose a
--     distinction it drew (@'qualifiedKey'@'s frames make @(alias, local)@
--     recoverable — 'Lara.Map.Types.parseQualifiedKey' is the operational
--     witness);
--   * across two members with __distinct aliases__ the renamed namespaces are
--     __disjoint__, so no member can capture another's leaf.
--
-- Both are mechanized in @lean\/Lara\/Map\/Qualify.lean@ (@mapLeaf_injective@,
-- @qualifiedKey_inj@), together with the transport results that say a renamed
-- term still checks and still concludes what it concluded.
--
-- == Why the namespaces are renamed separately
--
-- 'LeafId', 'ArgId' and 'GroupId' each get their own qualifier, even though the
-- three renames are the same string function underneath. They are separate
-- namespaces in "Lara.AST" and stay separate here, so a leaf identity can never
-- be handed to a function expecting an argument identity — the repo's rule that
-- separate namespaces get separate types, applied to the renaming as well as to
-- the names.
module Lara.Map.Qualify
  ( -- * Qualifying one local identity
    qualifyLeafId
  , qualifyArgId
  , qualifyGroupId
    -- * Qualifying the structures that reference them
  , qualifyTerm
  , qualifyAttack
  , qualifyGroup
    -- * A whole member's qualified material
  , QualifiedArgId
  , qualifiedArgId
  , LocalArgId
  , localArgId
  , asLocalArgId
  , QualifiedArg (..)
  , QualifiedMember (..)
  , qualifyMember
  ) where

import Lara.Map.Qualify.Internal (LocalArgId (..), QualifiedArgId (..))
import Lara.AST
  ( ArgId (..)
  , Attack (..)
  , DupGroup (..)
  , GroupId (..)
  , LeafId (..)
  , SupportTerm (..)
  , Unit (..)
  )
import Lara.Map.Types (MemberAlias, qualifiedKey, qualifyId)
import Lara.Prop (Prop)

-- ---------------------------------------------------------------------------
-- Qualifying one local identity
-- ---------------------------------------------------------------------------

-- | The one place a local name becomes a map-wide name: the length-framed
-- identity form of the @(alias, local)@ pair.
--
-- Private, and deliberately so: every caller goes through one of the three
-- namespace-specific wrappers below, which is what keeps a leaf name from being
-- renamed as though it were an argument name.
qualifiedName :: MemberAlias -> String -> String
qualifiedName alias local = qualifiedKey (qualifyId alias local)

-- | Qualify one member-local evidence-leaf identifier.
qualifyLeafId :: MemberAlias -> LeafId -> LeafId
qualifyLeafId alias (LeafId l) = LeafId (qualifiedName alias l)

-- | Qualify one member-local argument identifier.
qualifyArgId :: MemberAlias -> ArgId -> QualifiedArgId
qualifyArgId alias (ArgId a) = QualifiedArgId (ArgId (qualifiedName alias a))

-- | The underlying identifier, for the linked unit and the wire.
--
-- The wrapper itself is declared in "Lara.Map.Qualify.Internal"; 'qualifyArgId'
-- is the only way in from here, which is what makes a 'QualifiedArgId' mean
-- "this went through qualification" rather than merely "this is an 'ArgId'".
-- There is deliberately no @ArgId -> QualifiedArgId@ in this module: one would
-- contradict that claim two lines below where it is made. Tests that must forge
-- one use the @.Internal@ module.
qualifiedArgId :: QualifiedArgId -> ArgId
qualifiedArgId (QualifiedArgId a) = a

-- | The underlying identifier, for a verdict's reporting handle.
localArgId :: LocalArgId -> ArgId
localArgId (LocalArgId a) = a

-- | Mark an 'ArgId' as a member-local name.
--
-- Unlike 'qualifyArgId' this is a pure re-labelling, and that is honest: a local
-- name is whatever the member's author wrote, so there is no operation for the
-- wrapper to certify. The wrapper's job is to stop 'Lara.Map.Link' putting one
-- where an identity belongs, which it does regardless of how the value was
-- built.
asLocalArgId :: ArgId -> LocalArgId
asLocalArgId = LocalArgId

-- | Qualify one member-local duplicate-report-group identifier.
qualifyGroupId :: MemberAlias -> GroupId -> GroupId
qualifyGroupId alias (GroupId g) = GroupId (qualifiedName alias g)

-- ---------------------------------------------------------------------------
-- Qualifying the structures that reference them
-- ---------------------------------------------------------------------------

-- | Rename every leaf occurrence of a support term, and __nothing else__.
--
-- The recursion visits both places a 'SupportTerm' can hide a leaf: the premise
-- list and the critical-question discharge map. Everything else is carried
-- through verbatim, and each omission is a decision:
--
--   * 'srRule' names a rule of the __shared policy__, which every member of a
--     map has been shown to agree on ('Lara.Map.Types.CFPolicyStructure');
--   * 'srSubst' binds the rule's own parameters to ground terms built from the
--     __shared signature__ ('Lara.Map.Types.CFSignature');
--   * the discharge __keys__ are the policy's 'QuestionId's, so an answer
--     answers the same question in every member;
--   * 'srHoles' names obligations of that same rule;
--   * 'srAssurance' carries a backend, a theory digest, and a certificate whose
--     premise positions index the rule's premise list.
--
-- Renaming any of them would make one member's material unreadable against the
-- policy the map checks under.
--
-- This is the Haskell mirror of @mapLeaf@ in @lean\/Lara\/Map\/Qualify.lean@,
-- where the corresponding transport results are proved.
qualifyTerm :: MemberAlias -> SupportTerm -> SupportTerm
qualifyTerm alias = go
  where
    go term = case term of
      SLeaf l -> SLeaf (qualifyLeafId alias l)
      SRule rn theta premises discharge holes assurance ->
        SRule
          rn
          theta
          (map go premises)
          [(question, go answer) | (question, answer) <- discharge]
          holes
          assurance

-- | Rename both endpoints of a typed attack, keeping its kind and its position
-- path.
--
-- The __position is not qualified__, and that is the same split one level up: a
-- 'Lara.AST.StepPremise' is an index into the target rule's premise list and a
-- 'Lara.AST.StepQuestion' names one of that rule's critical questions. Both are
-- coordinates in the shared policy, not handles the member owns.
qualifyAttack :: MemberAlias -> Attack -> Attack
qualifyAttack alias attack = case attack of
  Rebut source target -> Rebut (arg source) (arg target)
  Undercut source target position -> Undercut (arg source) (arg target) position
  Undermine source target position -> Undermine (arg source) (arg target) position
  where
    -- An 'Attack' is a structure of the linked unit, so its endpoints are
    -- map-namespace identities; the wrapper is unwrapped at the boundary rather
    -- than pushed into "Lara.AST", which has no notion of a map.
    arg = qualifiedArgId . qualifyArgId alias

-- | Rename a duplicate-report group: its own identifier __and__ every member it
-- names, because those members are leaf identifiers of the same member and have
-- been renamed with it.
qualifyGroup :: MemberAlias -> DupGroup -> DupGroup
qualifyGroup alias (DupGroup gid members) =
  DupGroup (qualifyGroupId alias gid) (map (qualifyLeafId alias) members)

-- ---------------------------------------------------------------------------
-- A whole member's qualified material
-- ---------------------------------------------------------------------------

-- | One argument of one member, with __both__ names retained.
--
-- The pair is the point. 'qaQualified' is the identity the linked unit uses;
-- 'qaLocal' is the name the member's author wrote and the map reports under, so
-- a composite verdict can always say @(paper_a, a1)@ rather than
-- @7:paper_a2:a1@. Dropping either one would lose something no later stage can
-- recover: the qualified name is not a report, and the local name is not an
-- identity.
data QualifiedArg = QualifiedArg
  { qaLocal :: LocalArgId
  , qaQualified :: QualifiedArgId
  , qaTerm :: SupportTerm
  }
  deriving (Eq, Show)

-- | One member's material, with every local identity renamed into the map's
-- namespace.
--
-- __Not opaque, and carrying no promise.__ 'qualifyMember' is a total function
-- of a 'Lara.AST.Unit' and an alias; it neither checks nor assumes anything.
-- The promise a map rests on lives one stage back, on
-- 'Lara.Map.Load.CheckedMember', and one stage forward, on
-- 'Lara.Map.Link.LinkedMap' — this record is the derived data between them, and
-- hiding its constructor would suggest a guarantee it does not carry.
--
-- The policy-side fields of the member's 'Lara.AST.Unit' (signature, rules,
-- contraries, exceptions, theories) are deliberately absent: they are the
-- __shared contract__, identical across every member by
-- 'Lara.Map.Types.CFPolicyStructure' \/ 'Lara.Map.Types.CFSignature' \/
-- 'Lara.Map.Types.CFTheories', so carrying one copy per member would invite a
-- caller to pick one arbitrarily. "Lara.Map.Link" reads them from the members'
-- units directly, having first checked that they agree.
data QualifiedMember = QualifiedMember
  { qmAlias :: MemberAlias
  , -- | the member's leaf context, renamed; in the member's declaration order
    qmLeaves :: [(LeafId, Prop)]
  , -- | the member's arguments, renamed, in declaration order, each retaining
    -- the local name it was declared under
    qmArgs :: [QualifiedArg]
  , -- | the member's own declared attacks, renamed. These are transported
    -- unchanged into the linked unit: a map never rewrites, drops, or
    -- reinterprets an attack a member declared.
    qmAttacks :: [Attack]
  , -- | the member's queried claim atoms, __unrenamed__ — a proposition is a
    -- meaning, not a handle
    qmQueries :: [Prop]
  , -- | the member's duplicate-report groups, renamed
    qmGroups :: [DupGroup]
  }
  deriving (Eq, Show)

-- | Qualify a whole member's unit by its alias.
--
-- Order is preserved everywhere — leaves, arguments, attacks, queries, and
-- groups all come out in the member's own declaration order — because the
-- composite verdict's @nodes@ and @statuses@ sections are keyed by member order
-- and then by that member's own order, and a rename that reordered anything
-- would silently reorder a verdict.
qualifyMember :: MemberAlias -> Unit -> QualifiedMember
qualifyMember alias unit =
  QualifiedMember
    { qmAlias = alias
    , qmLeaves = [(qualifyLeafId alias l, p) | (l, p) <- unitLeaves unit]
    , qmArgs =
        [ QualifiedArg
            { qaLocal = asLocalArgId local
            , qaQualified = qualifyArgId alias local
            , qaTerm = qualifyTerm alias term
            }
        | (local, term) <- unitArgs unit
        ]
    , qmAttacks = map (qualifyAttack alias) (unitAttacks unit)
    , qmQueries = unitQueries unit
    , qmGroups = map (qualifyGroup alias) (unitGroups unit)
    }
