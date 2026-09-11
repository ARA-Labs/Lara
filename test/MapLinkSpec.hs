-- | Ground-truth tests for the map's qualification and linking stages
-- ("Lara.Map.Qualify" and "Lara.Map.Link").
--
-- Five things are pinned here, and they are the five the composite verdict
-- rests on:
--
--   * __qualification is what makes a map possible at all__ — two members that
--     each declare @e1@, @a1@, @g1@ and a claim called @c1@ are rejected outright
--     when their units are simply concatenated, and link cleanly once every
--     local identity is renamed by its member's alias
--     ('prop_unqualifiedMembersCollide' \/ 'prop_collidingMembersLink');
--   * __the rename preserves what the checker reads__ — every member argument
--     infers the same conclusion and the same open obligations before and after
--     qualification, and every attack the member declared survives as its
--     qualified image ('prop_qualifyPreservesSupport',
--     'prop_localAttacksTransported');
--   * __saturation finds real cross-member conflict and invents none__ — two
--     solo-justified claims become mutually contested, two members about
--     different settings stay justified and unattacked, and a generated
--     undermine onto a leaf argument propagates by subargument closure to every
--     argument containing that leaf ('prop_soloJustifiedBecomeContested',
--     'prop_differentSettingsDoNotAttack', 'prop_leafTargetUndermine' — which
--     asserts the propagated edge as well as the undermine's shape);
--   * __no handle is lost__ — the node table is a total map from every
--     @(member alias, local argument id)@ pair to a linked index, and it stays
--     total when the structural merge folds two members' terms into one, both on
--     synthesized members and through a real map whose policy has a
--     premise-less rule ('prop_nodesAreTotalProvenance',
--     'prop_mergeFoldsIdenticalTerms', 'prop_mergeFiresThroughAMap');
--   * __the result is deterministic__ — linking one loaded map twice produces
--     the same unit, nodes, labels, edges and statuses
--     ('prop_linkIsDeterministic').
--
-- The fixtures are built from the committed @examples\/A@ tree and from small
-- members written out here against the same committed
-- @empirical-v1.policy.lara@ bytes, so every member of every map in this file
-- runs under one shared contract without any fixture in the repository being
-- edited. Each test copies its tree into a fresh temporary directory, as
-- "MapLoadSpec" does, and the suite runs from the package root.
module MapLinkSpec (mapLinkSpecProps) where

import Data.List (isInfixOf, nub, sort)
import qualified Data.List.NonEmpty as NE
import System.FilePath ((</>))
import Test.QuickCheck

import Lara.AST
  ( ArgId (..)
  , Attack (..)
  , DupGroup (..)
  , GroupConflictMode (..)
  , GroupId (..)
  , Label (..)
  , LeafId (..)
  , PropId (..)
  , Rejection (..)
  , Status (..)
  , Step (..)
  , SupportTerm (..)
  , TheoryDigest (..)
  , Unit (..)
  )
import Lara.Driver (buildCertOk, buildGamma)
import Lara.Map.Link
  ( LinkedArg (..)
  , LinkedMap
  , linkMap
  , linkedArguments
  , linkedLeaves
  , sharedSections
  , lmEdges
  , lmGenerated
  , lmLabels
  , lmNodes
  , lmStatuses
  , lmUnit
  , mergeArguments
  , renameTable
  , repoint
  )
import Lara.Map.Load
  ( CheckedMember
  , CheckedMembers
  , checkedMembers
  , cmAlias
  , cmClaims
  , cmUnit
  , loadMap
  )
import Lara.Map.Load.Internal (CheckedMember (..))
import Lara.Map.Qualify.Internal (QualifiedArgId (..))
import Lara.Map.Qualify
  ( QualifiedArg (..)
  , QualifiedMember (..)
  , asLocalArgId
  , qualifiedArgId
  , qualifyArgId
  , qualifyGroupId
  , qualifyLeafId
  , qualifyMember
  , qualifyTerm
  )
import Lara.Map.Types
  ( MapError
  , MapNode (..)
  , MapStatus (..)
  , MemberAlias
  , aliasText
  , mkMemberAlias
  , mkNodeIndex
  , nodeIndexInt
  , renderMapError
  )
import Lara.SupportTerm (CheckLoc (LocRoot), inferSupport, srConclusion, srObligations)

import Lara.Check (checkUnit)
import Lara.Diagnostics (rejectionOf)
import Lara.Prop (Pred (..), Prop (..))
import Lara.Policy (lookupRule)
import Lara.Sigma (emptySigma)
import qualified Lara.TempTree as TempTree

-- ---------------------------------------------------------------------------
-- Fixtures on disk
-- ---------------------------------------------------------------------------

-- | Build a throwaway directory tree, run the body over its root, then remove
-- it. The one shared helper ("Lara.TempTree"), which reserves the directory
-- rather than deriving its name.
withTree :: [(FilePath, String)] -> (FilePath -> IO a) -> IO a
withTree = TempTree.withTree "lara-maplink"

-- | A @lara-map\@1@ manifest over the given member section, under the shared
-- @empirical-v1@ contract every fixture in this module uses.
manifestWith :: String -> String
manifestWith members =
  unlines
    [ "(lara-map@1"
    , "  (policy empirical-v1 empirical-v1.policy.lara)"
    , "  (backends (backend nd 1))"
    , "  (members " ++ members ++ ")"
    , "  (alignments)"
    , "  (questions))"
    ]

-- | One member's directory: its source and its own copy of the contract policy.
memberDir :: String -> String -> String -> [(FilePath, String)]
memberDir policy dir source =
  [ (dir ++ "/example.lara", source)
  , (dir ++ "/empirical-v1.policy.lara", policy)
  ]

-- | Load a map built from the given @(alias, directory, source)@ members.
loadFixture :: [(String, String, String)] -> IO (Either MapError CheckedMembers)
loadFixture members = do
  policy <- readFile "examples/A/empirical-v1.policy.lara"
  let manifest =
        manifestWith $
          unwords ["(member " ++ alias ++ " " ++ dir ++ "/example.lara)" | (alias, dir, _) <- members]
      tree =
        [ ("map.laramap", manifest)
        , ("empirical-v1.policy.lara", policy)
        ]
          ++ concat [memberDir policy dir source | (_, dir, source) <- members]
  withTree tree (\root -> loadMap (root </> "map.laramap"))

-- | Load a map and link it in one step.
linkFixture :: [(String, String, String)] -> IO (Either MapError LinkedMap)
linkFixture members = do
  loaded <- loadFixture members
  pure (loaded >>= linkMap)

-- ---------------------------------------------------------------------------
-- Member sources
-- ---------------------------------------------------------------------------

-- | @examples\/A@ plus a second report of one cell and the duplicate-report
-- group over the two.
--
-- The group is what makes @examples\/A@ a __group-id__ collision fixture as well
-- as a leaf-, argument- and claim-id one: two copies of this text under two
-- aliases both declare @g1@. Its two members carry the same proposition, so the
-- group is consistent, nothing is quarantined, and the member's admission audit
-- stays empty — a member with a nonempty audit is refused at load and would
-- never reach the linking stage at all.
--
-- Appended to the committed bytes rather than edited into them: no fixture in
-- the repository is touched by this suite.
groupTail :: String
groupTail =
  unlines
    [ ""
    , "leaf e10 : reports(exp_3, effect(M, accuracy, D, positive))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [evidence/table_2b.csv#row=mean]"
    , ""
    , "group g1 = [e1, e10]"
    ]

-- | A member whose single claim is @improves(M, accuracy, D)@ and which is
-- justified on its own: one complete argument, no attack.
posMember :: String
posMember =
  unlines
    [ "artifact paper_pos at sha256:pos..."
    , "policy empirical-v1"
    , "use backends [nd@1]"
    , ""
    , "claim c_pos"
    , "  nl      = \"Method M improves accuracy on distribution D\""
    , "  formal  = improves(M, accuracy, D)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "leaf a_e1 : reports(paperA_exp1, effect(M, accuracy, D, positive))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [paperA/table_2.csv#row=mean]"
    , ""
    , "leaf a_e2 : randomized(paperA_exp1)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [paperA.pdf#sec=4]"
    , ""
    , "leaf a_e3 : powered(paperA_exp1)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [paperA.pdf#sec=4]"
    , ""
    , "leaf a_e4 : generalizes(M, accuracy, D)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [paperA.pdf#sec=5]"
    , ""
    , "arg pa : supports(c_pos) by controlled_experiment(M, accuracy, D, paperA_exp1)"
    , "  discharge randomization     with a_e2"
    , "  discharge adequate_power    with a_e3"
    , "  discharge external_validity with a_e4"
    , ""
    , "status c_pos"
    ]

-- | The contradicting member: @not_improves(M, accuracy, D)@ on the same
-- @(system, measurand, dataset)@ atoms, justified on its own.
negMember :: String
negMember =
  unlines
    [ "artifact paper_neg at sha256:neg..."
    , "policy empirical-v1"
    , "use backends [nd@1]"
    , ""
    , "claim c_neg"
    , "  nl      = \"Method M does not improve accuracy on distribution D\""
    , "  formal  = not_improves(M, accuracy, D)"
    , "  binding = { author = bob, audit-status = reviewed }"
    , ""
    , "leaf b_e1 : reports(paperB_exp1, effect(M, accuracy, D, negligible))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [paperB/table_1.csv#row=mean]"
    , ""
    , "leaf b_e2 : randomized(paperB_exp1)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [paperB.pdf#sec=3]"
    , ""
    , "leaf b_e3 : powered(paperB_exp1)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [paperB.pdf#sec=3]"
    , ""
    , "arg pb : supports(c_neg) by null_result(M, accuracy, D, paperB_exp1)"
    , "  discharge randomization  with b_e2"
    , "  discharge adequate_power with b_e3"
    , ""
    , "status c_neg"
    ]

-- | The same shape as 'negMember', but about a __different setting__: system
-- @M_c@ on dataset @D_c@ rather than @M@ on @D@.
--
-- Nothing here is weaker than 'negMember' — it is the same rule instantiated at
-- other ground terms — so any attack it fails to draw is one no contrary
-- instance licensed. This is what makes it the negative control:
-- @not_improves(M_c, accuracy, D_c)@ and @improves(M, accuracy, D)@ are not a
-- declared contrary /instance/, because the policy's contrary patterns share
-- their parameters across both sides.
otherSettingMember :: String
otherSettingMember =
  unlines
    [ "artifact paper_other at sha256:other..."
    , "policy empirical-v1"
    , "use backends [nd@1]"
    , ""
    , "claim c_other"
    , "  nl      = \"Method M_c does not improve accuracy on distribution D_c\""
    , "  formal  = not_improves(M_c, accuracy, D_c)"
    , "  binding = { author = bob, audit-status = reviewed }"
    , ""
    , "leaf o_e1 : reports(exp_c, effect(M_c, accuracy, D_c, negligible))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [paperC/table_1.csv#row=mean]"
    , ""
    , "leaf o_e2 : randomized(exp_c)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [paperC.pdf#sec=3]"
    , ""
    , "leaf o_e3 : powered(exp_c)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [paperC.pdf#sec=3]"
    , ""
    , "arg po : supports(c_other) by null_result(M_c, accuracy, D_c, exp_c)"
    , "  discharge randomization  with o_e2"
    , "  discharge adequate_power with o_e3"
    , ""
    , "status c_other"
    ]

-- | 'posMember' with its external-validity leaf __also declared as an argument
-- of its own__.
--
-- That one extra declaration is what makes subargument propagation observable
-- across a member boundary: @ag@ is the term @leaf a_e4@, which is /also/ the
-- discharge subterm of @pa@. A cross-member undermine of @ag@ therefore reaches
-- @pa@ through 'Lara.Compile.coveredB' without any attack naming @pa@.
genMember :: String
genMember =
  unlines
    [ "artifact paper_gen at sha256:gen..."
    , "policy empirical-v1"
    , "use backends [nd@1]"
    , ""
    , "claim c_pos"
    , "  nl      = \"Method M improves accuracy on distribution D\""
    , "  formal  = improves(M, accuracy, D)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "leaf a_e1 : reports(paperA_exp1, effect(M, accuracy, D, positive))"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [paperA/table_2.csv#row=mean]"
    , ""
    , "leaf a_e2 : randomized(paperA_exp1)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [paperA.pdf#sec=4]"
    , ""
    , "leaf a_e3 : powered(paperA_exp1)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [paperA.pdf#sec=4]"
    , ""
    , "leaf a_e4 : generalizes(M, accuracy, D)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [paperA.pdf#sec=5]"
    , ""
    , "arg pa : supports(c_pos) by controlled_experiment(M, accuracy, D, paperA_exp1)"
    , "  discharge randomization     with a_e2"
    , "  discharge adequate_power    with a_e3"
    , "  discharge external_validity with a_e4"
    , ""
    , "arg ag : challenges(a_e1) by leaf(a_e4)"
    , ""
    , "status c_pos"
    ]

-- | A member asserting the declared contrary of @generalizes(M, accuracy, D)@
-- from a single leaf, so its one argument is __leaf-shaped__ and can itself be
-- undermined.
shiftMember :: String
shiftMember =
  unlines
    [ "artifact paper_shift at sha256:shift..."
    , "policy empirical-v1"
    , "use backends [nd@1]"
    , ""
    , "claim c_shift"
    , "  nl      = \"The reported result does not generalize\""
    , "  formal  = not_generalizes(M, accuracy, D)"
    , "  binding = { author = carol, audit-status = reviewed }"
    , ""
    , "leaf s_e1 : not_generalizes(M, accuracy, D)"
    , "  kind       = observed"
    , "  provenance = ai-executed"
    , "  refs       = [paperC.pdf#appendix=C]"
    , ""
    , "arg ps : supports(c_shift) by leaf(s_e1)"
    , ""
    , "status c_shift"
    ]

-- ---------------------------------------------------------------------------
-- Outcome assertions
-- ---------------------------------------------------------------------------

-- | The outcome linked, and the body has something to say about it.
expectLinked :: String -> Either MapError LinkedMap -> (LinkedMap -> Property) -> Property
expectLinked what outcome body =
  counterexample (what ++ ": " ++ either renderMapError (const "linked") outcome) $
    case outcome of
      Right linked -> body linked
      Left _ -> property False

-- | The outcome loaded, and the body has something to say about it.
expectLoaded :: String -> Either MapError CheckedMembers -> (CheckedMembers -> Property) -> Property
expectLoaded what outcome body =
  counterexample (what ++ ": " ++ either renderMapError (const "loaded") outcome) $
    case outcome of
      Right loaded -> body loaded
      Left _ -> property False

-- | An alias the tests name directly. Total on the spellings used here, which
-- are all bare ASCII identifiers.
aliasOf :: String -> MemberAlias
aliasOf name = case mkMemberAlias name of
  Just alias -> alias
  Nothing -> error ("MapLinkSpec: not a well-formed alias: " ++ name)

-- | The two-copies map: one text, two aliases, every local identity shared.
copiesFixture :: String -> [(String, String, String)]
copiesFixture source =
  [ ("paper_a", "a", source)
  , ("paper_a2", "a2", source)
  ]

-- | The @examples\/A@ text with the duplicate-report group appended.
readCollidingSource :: IO String
readCollidingSource = do
  paperA <- readFile "examples/A/example.lara"
  pure (paperA ++ groupTail)

-- ---------------------------------------------------------------------------
-- Qualification is what makes a map possible
-- ---------------------------------------------------------------------------

-- | __Before qualification, two colliding members do not compose.__
--
-- The two members of the fixture are the same text under two aliases: each
-- declares leaves @e1@ … @e10@, arguments @a1@, @d1@, @d2@, @d3@, a group @g1@,
-- and a claim @c1@. Concatenating their checked units — the naive link, with no
-- renaming — is refused by the ordinary checker for a duplicate argument, and
-- the two leaf contexts are not disjoint.
--
-- This is the test the qualification stage exists to make pass, so it is
-- deliberately written against the /unqualified/ material and left in place:
-- were the rename ever weakened to a no-op, this property would keep passing
-- and 'prop_collidingMembersLink' would start failing, which is the pair that
-- localises the fault.
prop_unqualifiedMembersCollide :: Property
prop_unqualifiedMembersCollide = once $ ioProperty $ do
  source <- readCollidingSource
  outcome <- loadFixture (copiesFixture source)
  pure $
    expectLoaded "two identical members" outcome $ \loaded ->
      case NE.toList (checkedMembers loaded) of
        [first, second] ->
          let left = cmUnit first
              right = cmUnit second
              naive =
                left
                  { unitLeaves = unitLeaves left ++ unitLeaves right
                  , unitArgs = unitArgs left ++ unitArgs right
                  , unitAttacks = unitAttacks left ++ unitAttacks right
                  , unitQueries = unitQueries left ++ unitQueries right
                  , unitGroups = unitGroups left ++ unitGroups right
                  }
              gamma = buildGamma (unitLeaves naive)
              certOk = buildCertOk (unitTheories naive)
           in conjoin
                [ counterexample "the two members' leaf identities overlap" $
                    property (not (null (leafIdsOf left `intersect'` leafIdsOf right)))
                , counterexample "the two members' argument identities overlap" $
                    property (not (null (argIdsOf left `intersect'` argIdsOf right)))
                , counterexample "the two members' group identities overlap" $
                    property (not (null (groupIdsOf left `intersect'` groupIdsOf right)))
                , counterexample "the two members declare a claim of the same name" $
                    map fst (cmClaims first) === map fst (cmClaims second)
                , counterexample "the naive concatenation is rejected by the checker" $
                    case checkUnit gamma certOk naive of
                      Left unitError -> rejectionOf unitError === DuplicateArgument
                      Right _ -> counterexample "accepted, which it must not be" (property False)
                ]
        members -> counterexample "expected exactly two members" (length members === 2)
  where
    intersect' xs ys = [x | x <- xs, x `elem` ys]
    leafIdsOf unit = map fst (unitLeaves unit)
    argIdsOf unit = map fst (unitArgs unit)
    groupIdsOf unit = map dgId (unitGroups unit)

-- | __The rename is injective per member and disjoint across members.__
--
-- The two halves are separate obligations and the length framing is what
-- supplies both. Injectivity per member is what stops a member from losing a
-- distinction it drew; disjointness across members is what stops one member from
-- capturing another's leaf.
--
-- The adversarial pair is the point of the second half: @(pa, x)@ and @(p, ax)@
-- concatenate to the same string under any framing-free scheme, and to
-- @2:pa1:x@ versus @1:p2:ax@ under this one. A test that only tried
-- @(pa, e1)@ against @(pb, e1)@ would pass for a scheme that simply glued the
-- two names together.
prop_qualifiedIdsAreDisjoint :: Property
prop_qualifiedIdsAreDisjoint = once $
  conjoin
    [ counterexample "injective within one member (leaves)" $
        property (qualifyLeafId a (LeafId "e1") /= qualifyLeafId a (LeafId "e2"))
    , counterexample "disjoint across members (leaves)" $
        property (qualifyLeafId a (LeafId "e1") /= qualifyLeafId b (LeafId "e1"))
    , counterexample "disjoint across members (arguments)" $
        property (qualifyArgId a (ArgId "a1") /= qualifyArgId b (ArgId "a1"))
    , counterexample "disjoint across members (groups)" $
        property (qualifyGroupId a (GroupId "g1") /= qualifyGroupId b (GroupId "g1"))
    , counterexample "no capture between a longer alias and a longer local name" $
        property (qualifyLeafId pa (LeafId "x") /= qualifyLeafId p (LeafId "ax"))
    ]
  where
    a = aliasOf "paper_a"
    b = aliasOf "paper_b"
    pa = aliasOf "pa"
    p = aliasOf "p"

-- | __After qualification, the same two members link.__
--
-- Every one of the four colliding namespaces is checked: the linked unit
-- declares eight arguments (four per member, none merged), sixteen leaf
-- identities with no repeat, two distinct groups, and a node table naming both
-- members' @a1@ at two different indices.
prop_collidingMembersLink :: Property
prop_collidingMembersLink = once $ ioProperty $ do
  source <- readCollidingSource
  outcome <- linkFixture (copiesFixture source)
  pure $
    expectLinked "two identical members, qualified" outcome $ \linked ->
      let unit = lmUnit linked
       in conjoin
            [ counterexample "no member's argument was merged away" $
                length (unitArgs unit) === 8
            , counterexample "the linked leaf identities are distinct" $
                length (nub (map fst (unitLeaves unit))) === length (unitLeaves unit)
            , counterexample "both members' groups survive, distinctly" $
                length (nub (map dgId (unitGroups unit))) === 2
            , counterexample "a group's members were renamed with its member" $
                property
                  ( and
                      [ member `elem` map fst (unitLeaves unit)
                      | group <- unitGroups unit
                      , member <- dgMembers group
                      ]
                  )
            , counterexample "both members' local a1 is reported, at two indices" $
                sort [nodeIndexInt (mnIndex node) | node <- lmNodes linked, mnArg node == ArgId "a1"]
                  === [0, 4]
            , counterexample "each member's claim keeps its own handle" $
                [(aliasText (msAlias s), msClaim s) | s <- lmStatuses linked]
                  === [("paper_a", PropId "c1"), ("paper_a2", PropId "c1")]
            ]

-- ---------------------------------------------------------------------------
-- The rename preserves what the checker reads
-- ---------------------------------------------------------------------------

-- | __Qualification preserves support typing.__
--
-- For every argument of every member: inferring under the member's own rules and
-- leaf context gives the same conclusion and the same open obligations as
-- inferring the /renamed/ term under the /renamed/ leaf context. Nothing about
-- what an argument concludes, or what it still owes, depends on the names its
-- leaves are spelled with.
--
-- This is the conformance witness for the mechanized statement:
-- @hasSupport_mapLeaf@ in @lean\/Lara\/Map\/Qualify.lean@ proves the same fact
-- relationally, for an arbitrary injective leaf rename and an arbitrary
-- environment that transports along it.
prop_qualifyPreservesSupport :: Property
prop_qualifyPreservesSupport = once $ ioProperty $ do
  source <- readCollidingSource
  outcome <- loadFixture (copiesFixture source)
  pure $
    expectLoaded "support typing across the rename" outcome $ \loaded ->
      conjoin (map preservedFor (NE.toList (checkedMembers loaded)))
  where
    preservedFor member =
      let unit = cmUnit member
          alias = cmAlias member
          qualified = qualifyMember alias unit
          pI = lookupRule (unitRules unit)
          certOk = buildCertOk (unitTheories unit)
          before = buildGamma (unitLeaves unit)
          after = buildGamma (qmLeaves qualified)
          infer gamma term = inferSupport pI gamma certOk LocRoot term
          summarise = fmap (\result -> (srConclusion result, srObligations result))
       in counterexample ("member " ++ aliasText alias) $
            conjoin
              [ counterexample ("argument " ++ show local) $
                  summarise (infer after (qualifyTerm alias term))
                    === summarise (infer before term)
              | (local, term) <- unitArgs unit
              ]

-- | __Every attack a member declared is transported unchanged.__
--
-- \"Unchanged\" means: same kind, same position path, endpoints renamed by the
-- member's own alias and by nothing else. A map never drops, rewrites, or
-- reinterprets an attack an author declared — it only adds the cross-member ones
-- the all-pairs conflict scan requires.
--
-- The fixture's member is @examples\/A@, which declares all three attack kinds
-- (an undercut at a rule position, an undermine at a nested discharge leaf, and
-- two rebuts), so the retained-undercut and retained-undermine cases are covered
-- by the same assertion.
prop_localAttacksTransported :: Property
prop_localAttacksTransported = once $ ioProperty $ do
  source <- readCollidingSource
  loaded <- loadFixture (copiesFixture source)
  outcome <- linkFixture (copiesFixture source)
  pure $
    expectLoaded "the loaded members" loaded $ \members ->
      expectLinked "the linked map" outcome $ \linked ->
        let unit = lmUnit linked
            expected =
              [ qualifyAttackOf (cmAlias member) attack
              | member <- NE.toList (checkedMembers members)
              , attack <- unitAttacks (cmUnit member)
              ]
         in conjoin
              [ counterexample "every declared attack survives, qualified" $
                  property (all (`elem` unitAttacks unit) expected)
              , counterexample "an undercut at a rule position is retained" $
                  property (any isUndercut expected && all (`elem` unitAttacks unit) (filter isUndercut expected))
              , counterexample "an undermine at a nested discharge position is retained" $
                  property (any (\k -> isUndermine k && not (null (positionOf k))) expected)
              , counterexample "the declared attacks come before the generated ones" $
                  take (length expected) (unitAttacks unit) === expected
              ]
  where
    qualifyAttackOf alias attack = case attack of
      Rebut source target -> Rebut (arg source) (arg target)
      Undercut source target position -> Undercut (arg source) (arg target) position
      Undermine source target position -> Undermine (arg source) (arg target) position
      where
        arg = qualifiedArgId . qualifyArgId alias
    isUndercut k = case k of Undercut{} -> True; _ -> False
    isUndermine k = case k of Undermine{} -> True; _ -> False
    positionOf k = case k of
      Rebut{} -> []
      Undercut _ _ position -> position
      Undermine _ _ position -> position

-- ---------------------------------------------------------------------------
-- Saturation finds real conflict and invents none
-- ---------------------------------------------------------------------------

-- | __Two solo-justified claims become mutually contested.__
--
-- Each member accepts on its own with its single claim @justified@ (asserted
-- here, not assumed). Linked, the saturation finds the declared contrary
-- instance between their conclusions, emits the rebut in both directions, and
-- the grounded labelling of the resulting two-cycle leaves both arguments
-- @undec@ — so both claims are @contested@.
--
-- Nothing in either member changed. This is the whole reason a map is worth
-- computing, and it is also why no monotonicity theorem is available anywhere in
-- this development: grounded status is not preserved when a framework grows.
prop_soloJustifiedBecomeContested :: Property
prop_soloJustifiedBecomeContested = once $ ioProperty $ do
  solo <- traverse (linkFixture . pure) [("paper_pos", "p", posMember), ("paper_neg", "n", negMember)]
  together <-
    linkFixture
      [ ("paper_pos", "p", posMember)
      , ("paper_neg", "n", negMember)
      ]
  pure $
    conjoin
      [ conjoin
          [ expectLinked "each member on its own" one $ \linked ->
              counterexample "justified alone" (map msStatus (lmStatuses linked) === [Justified])
          | one <- solo
          ]
      , expectLinked "the two-member map" together $ \linked ->
          conjoin
            [ counterexample "both claims are contested" $
                map msStatus (lmStatuses linked) === [Contested, Contested]
            , counterexample "both arguments are undec" $
                map snd (lmLabels linked) === [LUndec, LUndec]
            , counterexample "the saturation emitted exactly the two rebuts" $
                length (lmGenerated linked) === 2
            , counterexample "and they are rebuts, not undermines" $
                property (all isRebut (lmGenerated linked))
            , counterexample "the two-cycle is in the compiled edges" $
                map (\(i, j) -> (nodeIndexInt i, nodeIndexInt j)) (lmEdges linked)
                  === [(0, 1), (1, 0)]
            ]
      ]
  where
    isRebut k = case k of Rebut{} -> True; _ -> False

-- | __Two members about different settings do not attack each other.__
--
-- The negative control for the property above. @paper_other@ is @paper_neg@ with
-- its system and dataset changed to @M_c@ and @D_c@: the same rule, the same
-- shape, the same claim /form/. The policy's contrary patterns share their
-- parameters across both sides, so @not_improves(M_c, accuracy, D_c)@ is not a
-- contrary instance of @improves(M, accuracy, D)@ and no attack is licensed.
--
-- The saturation emits nothing, both claims stay @justified@, and the compiled
-- framework has no edges. A map that manufactured an attack here would be
-- reporting a disagreement the two papers do not have.
prop_differentSettingsDoNotAttack :: Property
prop_differentSettingsDoNotAttack = once $ ioProperty $ do
  outcome <-
    linkFixture
      [ ("paper_pos", "p", posMember)
      , ("paper_other", "o", otherSettingMember)
      ]
  pure $
    expectLinked "two members about different settings" outcome $ \linked ->
      conjoin
        [ counterexample "nothing was generated" (lmGenerated linked === [])
        , counterexample "no edges" (lmEdges linked === [])
        , counterexample "both arguments are in" $
            map snd (lmLabels linked) === [LIn, LIn]
        , counterexample "both claims stay justified" $
            map msStatus (lmStatuses linked) === [Justified, Justified]
        ]

-- | __A leaf-shaped argument is undermined at its root, and the undermine
-- propagates to every argument containing that leaf.__
--
-- @paper_gen@ declares @ag@, the term @leaf a_e4@, which is also the
-- external-validity discharge subterm of its main argument @pa@. @paper_shift@
-- concludes the declared contrary of @a_e4@'s proposition.
--
-- Two things are asserted, and they are different facts. First, the saturation
-- picks the shape the /target/ admits: a leaf target is undermined at the root
-- position, never rebutted. Second, the compiled edge from @ps@ reaches @pa@ —
-- index 0 — although no attack in the linked unit names @pa@ at all. That second
-- edge is ASPIC+ subargument closure crossing a member boundary, and it is what
-- turns @paper_gen@'s solo-justified claim into a contested one.
prop_leafTargetUndermine :: Property
prop_leafTargetUndermine = once $ ioProperty $ do
  outcome <-
    linkFixture
      [ ("paper_gen", "g", genMember)
      , ("paper_shift", "s", shiftMember)
      ]
  pure $
    expectLinked "a leaf-target undermine" outcome $ \linked ->
      let generated = lmGenerated linked
          edges = [(nodeIndexInt i, nodeIndexInt j) | (i, j) <- lmEdges linked]
          -- The argument at index 0 is asserted to be @paper_gen@'s @pa@ rather
          -- than taken on faith as \"whatever sits first\": the propagation
          -- claim below is about that argument specifically, and reading the
          -- head of the list would keep passing if the merge or the member
          -- order ever moved it.
          paArgId = qualifiedArgId (qualifyArgId (aliasOf "paper_gen") (ArgId "pa"))
          mentionsPa attack = paArgId `elem` endpointsOfAttack attack
       in conjoin
            [ counterexample "both generated attacks are root undermines" $
                property (all isRootUndermine generated)
            , counterexample "index 0 is paper_gen's own pa" $
                take 1 (map fst (unitArgs (lmUnit linked))) === [paArgId]
            , counterexample "the leaf argument is attacked from the other member" $
                property ((2, 1) `elem` edges)
            , counterexample "and the attack propagates to the argument containing that leaf" $
                property ((2, 0) `elem` edges)
            , -- Both endpoints, not just targets: the claim is that no attack
              -- mentions that argument at all, which is what makes the edge to it
              -- attributable to subargument closure and to nothing else.
              counterexample "no attack in the linked unit names that argument" $
                property (not (any mentionsPa (unitAttacks (lmUnit linked))))
            , counterexample "the solo-justified claim is now contested" $
                map msStatus (lmStatuses linked) === [Contested, Contested]
            ]
  where
    isRootUndermine k = case k of
      Undermine _ _ [] -> True
      _ -> False
    endpointsOfAttack attack = case attack of
      Rebut source target -> [source, target]
      Undercut source target _ -> [source, target]
      Undermine source target _ -> [source, target]

-- | __The saturation only crosses member boundaries.__
--
-- Every generated attack has a source declared by one member and a target
-- declared by another. A same-member pair is already the business of that
-- member's own declarations — its solo check ran the same all-pairs scan — and
-- generating for it would add edges the author never declared.
--
-- The fixture is the two-copies map, where each member has an internal contrary
-- pair (@a1@ concludes @improves@, @d3@ concludes @not_improves@) that it covers
-- with its own two rebuts. All four generated attacks must cross the boundary,
-- and none may duplicate a declared one.
prop_saturationIsCrossMemberOnly :: Property
prop_saturationIsCrossMemberOnly = once $ ioProperty $ do
  source <- readCollidingSource
  outcome <- linkFixture (copiesFixture source)
  pure $
    expectLinked "cross-member-only saturation" outcome $ \linked ->
      let owners = ownersByArgId linked
          crosses attack =
            let (from, to) = endpointsOf attack
             in lookup from owners /= lookup to owners
       in conjoin
            [ counterexample "four cross-boundary rebuts were generated" $
                length (lmGenerated linked) === 4
            , counterexample "every one of them crosses the member boundary" $
                property (all crosses (lmGenerated linked))
            , counterexample "and none of them duplicates a declared attack" $
                length (nub (unitAttacks (lmUnit linked))) === length (unitAttacks (lmUnit linked))
            , -- The module header promises this order, and a verdict's bytes
              -- depend on it: the generated attacks must come out in ascending
              -- @(source position, target position)@, which is the nested-loop
              -- order of the saturation and not the result of any sort.
              counterexample "generated in ascending (source, target) position" $
                let positions =
                      [ (positionOf linked from, positionOf linked to)
                      | attack <- lmGenerated linked
                      , let (from, to) = endpointsOf attack
                      ]
                 in positions === sort positions .&&. length (nub positions) === length positions
            ]
  where
    endpointsOf attack = case attack of
      Rebut source target -> (source, target)
      Undercut source target _ -> (source, target)
      Undermine source target _ -> (source, target)
    -- The position of a linked argument, by its identity in the linked unit.
    positionOf linked argId =
      length (takeWhile ((/= argId) . fst) (unitArgs (lmUnit linked)))
    ownersByArgId linked =
      [ (mnArgIdOf linked node, aliasText (mnAlias node))
      | node <- lmNodes linked
      ]
    mnArgIdOf linked node =
      case drop (nodeIndexInt (mnIndex node)) (unitArgs (lmUnit linked)) of
        ((argId, _) : _) -> argId
        [] -> ArgId ""

-- ---------------------------------------------------------------------------
-- No handle is lost
-- ---------------------------------------------------------------------------

-- | __The node table is a total, index-sound map from every original handle.__
--
-- One entry per @(member alias, local argument id)@ that any member declared,
-- no entry repeated, every index inside the linked argument list, and the term
-- at that index equal to the member's own qualified term. That last clause is
-- the one that makes the mapping /sound/ rather than merely total: an index
-- table that pointed every handle at argument 0 would satisfy the first three.
prop_nodesAreTotalProvenance :: Property
prop_nodesAreTotalProvenance = once $ ioProperty $ do
  source <- readCollidingSource
  loaded <- loadFixture (copiesFixture source)
  outcome <- linkFixture (copiesFixture source)
  pure $
    expectLoaded "the loaded members" loaded $ \members ->
      expectLinked "the linked map" outcome $ \linked ->
        let declared =
              [ (cmAlias member, local, qualifyTerm (cmAlias member) term)
              | member <- NE.toList (checkedMembers members)
              , (local, term) <- unitArgs (cmUnit member)
              ]
            args = unitArgs (lmUnit linked)
            nodes = lmNodes linked
            handleOf node = (mnAlias node, mnArg node)
            termAt i = case drop i args of
              ((_, term) : _) -> Just term
              [] -> Nothing
         in conjoin
              [ counterexample "one node per declared argument, in that order" $
                  map handleOf nodes === [(alias, local) | (alias, local, _) <- declared]
              , counterexample "no handle occurs twice" $
                  length (nub (map handleOf nodes)) === length nodes
              , counterexample "every node index resolves to the member's own term" $
                  [termAt (nodeIndexInt (mnIndex node)) | node <- nodes]
                    === [Just term | (_, _, term) <- declared]
              ]

-- | __The structural merge folds identical terms and keeps both handles.__
--
-- Exercised directly on synthesized members, where every field of the result
-- can be spelled out. A real map reaches the merge only through a leaf-free
-- term: "Lara.Map.Qualify" renames every leaf occurrence by its member's alias,
-- so a term mentioning a leaf can only collide with a term of the same member.
-- Neither shipped policy has a premise-less rule, so only the map fixture
-- written for it does ('prop_mergeFiresThroughAMap').
--
-- Two members declare one shared term under different local names and one
-- private term each. The result is three linked arguments, four handles, and the
-- shared term owned by both members at one index.
prop_mergeFoldsIdenticalTerms :: Property
prop_mergeFoldsIdenticalTerms = once $
  let shared = SLeaf (LeafId "shared")
      left = SLeaf (LeafId "left-only")
      right = SLeaf (LeafId "right-only")
      (linkedArgs, handles) =
        mergeArguments
          [ synthMember "one" [("x", shared), ("y", left)] []
          , synthMember "two" [("z", shared), ("w", right)] []
          ]
   in conjoin
        [ counterexample "the shared term became one linked argument" $
            map laTerm linkedArgs === [shared, left, right]
        , counterexample "the first member's name won the merge" $
            map laArgId linkedArgs === [ArgId "one:x", ArgId "one:y", ArgId "two:w"]
        , counterexample "and both members are recorded as its owners" $
            map laOwners linkedArgs
              === [[aliasOf "one", aliasOf "two"], [aliasOf "one"], [aliasOf "two"]]
        , counterexample "every declared handle survives, pointing at its term" $
            handles
              === [ (aliasOf "one", asLocalArgId (ArgId "x"), 0)
                  , (aliasOf "one", asLocalArgId (ArgId "y"), 1)
                  , (aliasOf "two", asLocalArgId (ArgId "z"), 0)
                  , (aliasOf "two", asLocalArgId (ArgId "w"), 2)
                  ]
        , counterexample "positions are the linked list positions" $
            map laIndex linkedArgs === [0, 1, 2]
        ]

-- | A synthesized qualified member: local names, terms, and declared attacks,
-- with the qualified identity spelled @alias:local@.
--
-- The spelling is deliberately __not__ 'Lara.Map.Types.qualifiedKey'. These
-- members exist to exercise the merge and the endpoint re-pointing, which are
-- indifferent to how an identity is spelled, and a readable identity makes the
-- expected values in these two properties legible. Nothing here is fed to the
-- checker.
synthMember :: String -> [(String, SupportTerm)] -> [Attack] -> QualifiedMember
synthMember alias entries attacks =
  QualifiedMember
    { qmAlias = aliasOf alias
    , qmLeaves = []
    , qmArgs =
        [ QualifiedArg
            { qaLocal = asLocalArgId (ArgId local)
            , qaQualified = QualifiedArgId (ArgId (alias ++ ":" ++ local))
            , qaTerm = term
            }
        | (local, term) <- entries
        ]
    , qmAttacks = attacks
    , qmQueries = []
    , qmGroups = []
    }

-- ---------------------------------------------------------------------------
-- The structural tripwires
-- ---------------------------------------------------------------------------

-- | Each structural failure arm refuses the condition it names.
--
-- These seven sites are dead under the suite, and a reviewer confirmed they are
-- genuinely unreachable through 'linkMap' given what the loader has already
-- established: leaf qualification confines a term collision to one member, and
-- the loader refuses two members sharing an alias. That makes them a missing
-- __tripwire__ rather than a hidden bug — and the concern is not that they are
-- wrong today, it is that nothing would notice the day the saturation and the
-- attack checker come apart. The decision record says a change there would
-- "deserve an anchor at that point"; this is that anchor, so there is now
-- something to break.
--
-- Each arm is driven on synthesized inputs, which is the only way to reach it:
-- 'linkedLeaves' and 'linkedArguments' take already-exported types, and
-- 'sharedSections' takes 'CheckedMember's, which "Lara.Map.Load.Internal"
-- exists to let a test build.
prop_structuralTripwires :: Property
prop_structuralTripwires = once $ ioProperty $ do
  sources <- readCollidingSource
  loaded <- loadFixture (copiesFixture sources)
  pure $ case loaded of
    Left err -> counterexample ("fixture did not load: " ++ renderMapError err) (property False)
    Right members ->
      let member = NE.head (checkedMembers members)
          -- One member's own unit, with one shared section replaced. Every
          -- field of SharedSections gets a row, so an added field without a
          -- row fails the arity check below rather than being uncovered.
          differing field unit = case field of
            "signature" -> unit {unitSigma = emptySigma}
            "rules" -> unit {unitRules = []}
            "contraries" -> unit {unitContraries = []}
            "exceptions" -> unit {unitExceptions = []}
            "theories" -> unit {unitTheories = [(TheoryDigest "sha256:absent", [])]}
            "duplicate-report mode" -> unit {unitGroupMode = RejectOnConflict}
            _ -> unit
          fields =
            [ "signature", "rules", "contraries", "exceptions"
            , "theories", "duplicate-report mode"
            ]
          peer field = withUnit (differing field (cmUnit member)) member
          sharedFor field = sharedSections member [peer field]
          -- Two members declaring one leaf identity, which qualification
          -- makes unreachable through linkMap.
          collidingLeaves =
            linkedLeaves
              [ synthMemberWithLeaves "one" [(LeafId "shared", tripwireProp)]
              , synthMemberWithLeaves "two" [(LeafId "shared", tripwireProp)]
              ]
          -- Two linked arguments under one identity, likewise.
          collidingArgs =
            linkedArguments
              [ LinkedArg (ArgId "same") (SLeaf (LeafId "x")) 0 [aliasOf "one"]
              , LinkedArg (ArgId "same") (SLeaf (LeafId "y")) 1 [aliasOf "two"]
              ]
       in conjoin
            [ counterexample "every shared section has a row" $
                length fields === 6
            , counterexample "a disagreeing shared section is refused, naming the field" $
                conjoin
                  [ counterexample field $ case sharedFor field of
                      Left err -> property (field `isInfixOf` renderMapError err)
                      Right _ ->
                        counterexample "accepted; the arm did not fire" (property False)
                  | field <- fields
                  ]
            , counterexample "an agreeing peer is accepted (the control)" $
                case sharedSections member [member] of
                  Right _ -> property True
                  Left err ->
                    counterexample ("refused: " ++ renderMapError err) (property False)
            , counterexample "two members declaring one leaf identity are refused" $
                case collidingLeaves of
                  Left err ->
                    property ("declare the leaf identity" `isInfixOf` renderMapError err)
                  Right _ -> counterexample "accepted" (property False)
            , counterexample "two linked arguments sharing an identity are refused" $
                case collidingArgs of
                  Left err ->
                    property ("share the identity" `isInfixOf` renderMapError err)
                  Right _ -> counterexample "accepted" (property False)
            ]

-- | A member with the given unit, everything else unchanged.
--
-- Built through "Lara.Map.Load.Internal", which is the only way: a
-- 'CheckedMember' promises the loader rechecked it, and a peer disagreeing on
-- a shared section is precisely a value the loader would never produce.
withUnit :: Unit -> CheckedMember -> CheckedMember
withUnit unit (CheckedMember alias path artifact _ replayId claims) =
  CheckedMember alias path artifact unit replayId claims

-- | Any proposition; the tripwire tests turn on identity, never on content.
tripwireProp :: Prop
tripwireProp = Prop (Pred "tripwire") []

-- | A synthesized qualified member carrying the given leaves and no arguments.
synthMemberWithLeaves :: String -> [(LeafId, Prop)] -> QualifiedMember
synthMemberWithLeaves alias leaves =
  (synthMember alias [] []) {qmLeaves = leaves}

-- | __When the merge fires, a declared attack's endpoints are re-pointed at the
-- surviving identity.__
--
-- This is the code path the merge exists for. 'Lara.Map.Link.mergeArguments'
-- folds two members' identical terms into one linked argument named by the
-- __first__ member, which leaves the second member's own attacks naming an
-- identity the linked unit no longer declares. Re-pointing is what stops them
-- dangling — and a dangling endpoint would not be reported by the checker but
-- silently dropped by 'Lara.Check.resolveAttacks', so nothing downstream would
-- notice.
--
-- Synthesized for the same reason 'prop_mergeFoldsIdenticalTerms' is, so that
-- each shape of re-pointing can be stated on its own;
-- 'prop_mergeFiresThroughAMap' is the same path reached through 'linkMap'.
prop_mergeRepointsAttackEndpoints :: Property
prop_mergeRepointsAttackEndpoints = once $
  let shared = SLeaf (LeafId "shared")
      private = SLeaf (LeafId "two-only")
      one = synthMember "one" [("x", shared)] []
      two =
        synthMember
          "two"
          [("z", shared), ("w", private)]
          [Rebut (ArgId "two:z") (ArgId "two:w")]
      (linkedArgs, _) = mergeArguments [one, two]
      table = renameTable linkedArgs [one, two]
      soloTable = renameTable (fst (mergeArguments [one])) [one]
   in conjoin
        [ counterexample "the merged-away identity maps to the surviving one" $
            lookup (ArgId "two:z") table === Just (ArgId "one:x")
        , counterexample "an unmerged identity maps to itself" $
            lookup (ArgId "two:w") table === Just (ArgId "two:w")
        , counterexample "the second member's declared attack is re-pointed" $
            repoint table (Rebut (ArgId "two:z") (ArgId "two:w"))
              === Rebut (ArgId "one:x") (ArgId "two:w")
        , counterexample "both endpoints move when both were merged" $
            repoint table (Rebut (ArgId "two:z") (ArgId "two:z"))
              === Rebut (ArgId "one:x") (ArgId "one:x")
        , counterexample "kind and position path survive re-pointing" $
            repoint table (Undermine (ArgId "two:z") (ArgId "two:w") [StepPremise 1])
              === Undermine (ArgId "one:x") (ArgId "two:w") [StepPremise 1]
        , counterexample "every re-pointed endpoint is a declared linked argument" $
            property
              ( all
                  (`elem` map laArgId linkedArgs)
                  (concatMap endpointsOfAttack (map (repoint table) (qmAttacks two)))
              )
        , counterexample "with nothing merged, re-pointing is the identity" $
            repoint soloTable (Rebut (ArgId "one:x") (ArgId "one:x"))
              === Rebut (ArgId "one:x") (ArgId "one:x")
        ]
  where
    endpointsOfAttack = attackEndpoints

-- | Both endpoints of an attack, whatever its kind.
attackEndpoints :: Attack -> [ArgId]
attackEndpoints attack = case attack of
  Rebut source target -> [source, target]
  Undercut source target _ -> [source, target]
  Undermine source target _ -> [source, target]

-- | __The structural merge fires through a real map__ (issue #316).
--
-- @test\/fixtures\/map\/merge\/@ runs under @convention-v1@, whose
-- @community_convention@ rule has no premises, and both of its members declare
-- an argument @conv@ by that rule on the same arguments. A leaf-free term has
-- nothing for qualification to rename, so the two members' terms are equal and
-- 'linkMap' is the thing that has to fold them. Everything the synthesized
-- properties above state separately is asserted here on one linked map:
--
--   * two handles, @(paper_adopt, conv)@ and @(paper_critic, conv)@, name one
--     linked index, and the unit carries two arguments for three handles;
--   * paper_critic's declared rebuttals are re-pointed at the argument the
--     merge kept, so every attack endpoint is a declared linked argument and
--     paper_critic's own identity for @conv@ is declared by nobody;
--   * the saturation's co-owned pair — @conv@, owned by both members, against
--     @crit@, owned by paper_critic alone — generates the same two rebuttals
--     paper_critic declared, and the dedupe leaves one copy of each;
--   * paper_adopt's claim, justified on its own, is contested in the map.
prop_mergeFiresThroughAMap :: Property
prop_mergeFiresThroughAMap = once $ ioProperty $ do
  loaded <- loadMap "test/fixtures/map/merge/map.laramap"
  pure $ case loaded of
    Left err -> counterexample ("merge fixture did not load: " ++ renderMapError err) (property False)
    Right members ->
      expectLinked "the merge map" (linkMap members) $ \linked ->
        let unit = lmUnit linked
            argIds = map fst (unitArgs unit)
            criticConv =
              [ qualifiedArgId (qaQualified arg)
              | m <- NE.toList (checkedMembers members)
              , aliasText (cmAlias m) == "paper_critic"
              , arg <- qmArgs (qualifyMember (cmAlias m) (cmUnit m))
              , qaLocal arg == asLocalArgId (ArgId "conv")
              ]
         in conjoin
              [ counterexample "two handles, one linked index" $
                  [ (aliasText (mnAlias n), mnArg n, nodeIndexInt (mnIndex n))
                  | n <- lmNodes linked
                  ]
                    === [ ("paper_adopt", ArgId "conv", 0)
                        , ("paper_critic", ArgId "conv", 0)
                        , ("paper_critic", ArgId "crit", 1)
                        ]
              , counterexample "two linked arguments for three handles" $
                  length argIds === 2
              , counterexample "paper_critic's own identity for conv was merged away" $
                  conjoin
                    [ counterexample "paper_critic's qualified conv was found" (length criticConv === 1)
                    , counterexample "and the linked unit does not declare it" $
                        property (not (any (`elem` argIds) criticConv))
                    ]
              , counterexample "every attack endpoint is a declared linked argument" $
                  property (all (`elem` argIds) (concatMap attackEndpoints (unitAttacks unit)))
              , counterexample "the dedupe leaves one rebuttal each way" $
                  length (unitAttacks unit) === 2
              , counterexample "the saturation generated both, and both are in the unit" $
                  conjoin
                    [ length (lmGenerated linked) === 2
                    , property (all (`elem` unitAttacks unit) (lmGenerated linked))
                    ]
              , counterexample "paper_adopt's solo-justified claim is contested in the map" $
                  [ (aliasText (msAlias s), msClaim s, msStatus s)
                  | s <- lmStatuses linked
                  ]
                    === [ ("paper_adopt", PropId "c_std", Contested)
                        , ("paper_critic", PropId "c_convention", Contested)
                        , ("paper_critic", PropId "c_objection", Contested)
                        ]
              ]

-- | __The linked unit's argument identities are the qualified ones, and they are
-- distinct.__
--
-- The argument-id half of R14, which 'Lara.Check.checkUnit' takes as an input
-- contract and does not recheck. It is asserted here on the two-copies fixture,
-- where both members declare @a1@, @d1@, @d2@ and @d3@, so an identity rename
-- that lost the alias would collide on all four.
--
-- Both clauses are needed and neither implies the other. Distinctness is the
-- invariant the checker relies on; the exact spelling is what pins /which/
-- rename produced it, so a rename that made identities unique by some other
-- means — a counter, say — would still be caught.
--
-- This is the property that fails if 'Lara.Map.Qualify.qualifyArgId' is weakened
-- to the identity; the collision and provenance tests do not, because eight
-- arguments and two node indices survive that change unaltered.
prop_linkedArgumentIdsAreQualified :: Property
prop_linkedArgumentIdsAreQualified = once $ ioProperty $ do
  source <- readCollidingSource
  outcome <- linkFixture (copiesFixture source)
  pure $
    expectLinked "qualified, distinct argument identities" outcome $ \linked ->
      let ids = map fst (unitArgs (lmUnit linked))
          expected =
            [ qualifiedArgId (qualifyArgId (aliasOf alias) (ArgId local))
            | alias <- ["paper_a", "paper_a2"]
            , local <- ["a1", "d1", "d2", "d3"]
            ]
       in conjoin
            [ counterexample "no two linked arguments share an identity" $
                length (nub ids) === length ids
            , counterexample "and each is its member's qualified spelling" $
                ids === expected
            , counterexample "every attack endpoint is a declared argument" $
                property
                  (all (`elem` ids) (concatMap endpointsOfAttack (unitAttacks (lmUnit linked))))
            ]
  where
    endpointsOfAttack attack = case attack of
      Rebut source target -> [source, target]
      Undercut source target _ -> [source, target]
      Undermine source target _ -> [source, target]

-- ---------------------------------------------------------------------------
-- Determinism
-- ---------------------------------------------------------------------------

-- | __Linking depends on the manifest and the members' declaration order, and on
-- nothing else.__
--
-- The two runs load the __same manifest from two different temporary
-- directories__, so every absolute path differs and every manifest-spelled path
-- agrees. The unit, the node table, the labels, the edges and the statuses must
-- come out identical.
--
-- Comparing @linkMap members@ against itself would prove nothing — that holds for
-- any pure function, including one that sorted the arguments by 'Ord' 'ArgId' or
-- reversed member order. Two independent loads are what make the property say
-- something: the composite verdict is a byte-for-byte artifact, and two people
-- running one manifest from two checkouts must get the same bytes.
prop_linkIsDeterministic :: Property
prop_linkIsDeterministic = once $ ioProperty $ do
  source <- readCollidingSource
  first <- linkFixture (copiesFixture source)
  second <- linkFixture (copiesFixture source)
  pure $
    expectLinked "the first load" first $ \one ->
      expectLinked "the second load, from a different directory" second $ \other ->
        conjoin
          [ counterexample "unit" (lmUnit one === lmUnit other)
          , counterexample "nodes" (lmNodes one === lmNodes other)
          , counterexample "labels" (lmLabels one === lmLabels other)
          , counterexample "edges" (lmEdges one === lmEdges other)
          , counterexample "generated attacks" (lmGenerated one === lmGenerated other)
          , counterexample "statuses" $
              map statusRow (lmStatuses one) === map statusRow (lmStatuses other)
          ]
  where
    statusRow s = (msAlias s, msClaim s, msStatus s)

-- | __Labels cover exactly the linked arguments, and edges stay in range.__
--
-- The invariant the composite verdict's decoder already enforces on its own
-- bytes ("Lara.Map.Wire"), asserted here on the values that will produce them,
-- so a producer defect is caught before the codec has to reject its own output.
prop_labelsAndEdgesAreWellFormed :: Property
prop_labelsAndEdgesAreWellFormed = once $ ioProperty $ do
  source <- readCollidingSource
  outcome <- linkFixture (copiesFixture source)
  pure $
    expectLinked "well-formed labels and edges" outcome $ \linked ->
      let n = length (unitArgs (lmUnit linked))
          labelIndices = map (nodeIndexInt . fst) (lmLabels linked)
          edgePairs = [(nodeIndexInt i, nodeIndexInt j) | (i, j) <- lmEdges linked]
       in conjoin
            [ counterexample "labels cover 0 .. n-1 ascending" $
                labelIndices === [0 .. n - 1]
            , counterexample "edge endpoints are in range" $
                property (all (\(i, j) -> i < n && j < n) edgePairs)
            , counterexample "edges are strictly ascending lexicographic" $
                property (and (zipWith (<) edgePairs (drop 1 edgePairs)))
            , counterexample "every node index is a valid NodeIndex" $
                property (all (\node -> mkNodeIndex (nodeIndexInt (mnIndex node)) /= Nothing) (lmNodes linked))
            ]

-- ---------------------------------------------------------------------------
-- Registration
-- ---------------------------------------------------------------------------

mapLinkSpecProps :: [(String, IO Result)]
mapLinkSpecProps =
  [ ("map unqualified members collide", quickCheckResult prop_unqualifiedMembersCollide)
  , ("map structural tripwires", quickCheckResult prop_structuralTripwires)
  , ("map qualified identities are disjoint", quickCheckResult prop_qualifiedIdsAreDisjoint)
  , ("map colliding members link once qualified", quickCheckResult prop_collidingMembersLink)
  , ("map qualification preserves support typing", quickCheckResult prop_qualifyPreservesSupport)
  , ("map local attacks are transported", quickCheckResult prop_localAttacksTransported)
  , ("map solo-justified claims become contested", quickCheckResult prop_soloJustifiedBecomeContested)
  , ("map different settings do not attack", quickCheckResult prop_differentSettingsDoNotAttack)
  , ("map leaf-target undermine propagates", quickCheckResult prop_leafTargetUndermine)
  , ("map saturation is cross-member only", quickCheckResult prop_saturationIsCrossMemberOnly)
  , ("map nodes are total provenance", quickCheckResult prop_nodesAreTotalProvenance)
  , ("map merge folds identical terms", quickCheckResult prop_mergeFoldsIdenticalTerms)
  , ("map merge re-points attack endpoints", quickCheckResult prop_mergeRepointsAttackEndpoints)
  , ("map merge fires through a real map", quickCheckResult prop_mergeFiresThroughAMap)
  , ("map linked argument ids are qualified", quickCheckResult prop_linkedArgumentIdsAreQualified)
  , ("map linking is deterministic", quickCheckResult prop_linkIsDeterministic)
  , ("map labels and edges are well-formed", quickCheckResult prop_labelsAndEdgesAreWellFormed)
  ]
