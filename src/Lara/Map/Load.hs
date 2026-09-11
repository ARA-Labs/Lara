-- | Stage two of the multi-artifact map: turn a @.laramap@ manifest on disk
-- into the map's members, each one rechecked on its own and agreed with the
-- manifest's shared contract.
--
-- == Position in the pipeline
--
-- @
-- .laramap bytes -> decode  ("Lara.Map.Wire")
--                -> resolve member paths against the MANIFEST's directory   <- here
--                -> load and recheck each member  ("Lara.Source.Load")
--                -> compare each member to the manifest's shared contract   <- here
--                -> qualify + link  ("Lara.Map.Qualify" \/ "Lara.Map.Link")
--                -> composite verdict  (\@Lara.Map.Driver\@, issue #303)
-- @
--
-- Every stage above has landed (issue #303): qualification and linking consume
-- this module through 'Lara.Map.Link.linkMap', and the @.laramap@ driver
-- consumes both through 'Lara.Map.Driver.runMap', which is what @lara check
-- \<file.laramap\>@ runs. 'loadMap' is this module's whole public surface, and
-- it returns 'CheckedMembers': the manifest, plus one 'CheckedMember' per
-- member carrying exactly what those stages need and nothing else. Every
-- filesystem access a map performs happens here, so every question about
-- /which bytes/ a map was run over is settled at this stage.
--
-- == A map is a recheck, not a build
--
-- Nothing here hashes a member, writes a lockfile, consults an mtime, or keeps
-- anything between runs. Each invocation reads the members' current bytes and
-- rechecks them. The 'Lara.Source.Load.SourceCache' this module creates is
-- per-invocation and exists for the opposite reason a build cache does: so that
-- one run reads one file exactly __once__, and two references to a shared
-- policy file cannot see two different versions of it. A source edit that
-- leaves the mtime untouched is therefore evaluated normally on the next run —
-- there is no staleness test to fool.
--
-- == Paths resolve against the manifest, never the working directory
--
-- Every declared path is resolved against @takeDirectory@ of the manifest's own
-- path. Two people running one manifest from different directories load the
-- same files, and a manifest is movable as a directory tree. Absolute and
-- parent-relative spellings both work, because @'System.FilePath.</>'@ already
-- returns an absolute right-hand side unchanged.
--
-- The resolved path is a plain 'FilePath' and stays one: 'DeclaredPath' is what
-- the verdict reports, and a 'CheckedMember' carries only the manifest-spelled
-- form, so no resolved absolute path can reach the composite verdict's bytes.
--
-- == Why 'CheckedMembers' is opaque
--
-- A 'CheckedMember' is a promise: this member was read from disk, elaborated,
-- rechecked, found to accept, found to carry an empty admission audit, and
-- found to agree with the manifest. The linking stage builds on all five, so
-- the constructor is hidden and the only way to obtain one is 'loadMap'. Were
-- the constructor exported, a caller could assemble a \"checked\" member out of
-- a 'Lara.AST.Unit' nothing had checked, and every guarantee the composite
-- verdict rests on would become a convention.
--
-- == What this module does not do
--
-- Reference resolution — 'MBUnknownAlias', 'MBUnknownClaim',
-- 'MBCoordinateOutOfRange', and a question's 'MBMixedSelector' — is /not/ here,
-- and it is not in "Lara.Map.Link" either. It needs each member's claim list,
-- which is exactly what 'cmClaims' hands onward, and it belongs beside the
-- alignment evaluation that consumes the same coordinates (issue #303).
-- Nothing in this module reads
-- 'Lara.Map.Types.mapAlignments' or 'Lara.Map.Types.mapQuestions'; both travel
-- through unread on 'checkedManifest'.
module Lara.Map.Load
  ( -- * Loading a map's members
    loadMap
  , loadMapWith
    -- * The checked members
  , CheckedMembers
  , checkedManifest
  , checkedMembers
  , CheckedMember
  , cmAlias
  , cmDeclaredPath
  , cmArtifact
  , cmUnit
  , cmReplayId
  , cmClaims
  ) where

import Data.List (sort)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import System.FilePath (takeDirectory, (</>))

import Lara.AST
  ( Decl (DeclClaim)
  , Digest
  , Policy
  , Program
  , PropId
  , Unit
  , claimFormal
  , claimId
  , policyId
  , policySigma
  , policyTheories
  , programBackends
  , programDecls
  , programPolicy
  , unitSigma
  , unitTheories
  )
import Lara.Admission
  ( admissionAuditIsEmpty
  , renderAdmissionAudit
  , renderAdmissionRejection
  )
import Lara.Elaborate
  ( PreparedSource (..)
  , runSourceCheck
  , sourceResultAudit
  , sourceResultCheckInput
  , sourceResultVerdict
  )
import Lara.Map.Load.Internal (CheckedMember (..), CheckedMembers (..))
import Lara.Map.Types
  ( ContractField (..)
  , DeclaredPath
  , MapBoundaryError (..)
  , MapError (..)
  , MapManifest (..)
  , MapMember (..)
  , MapRejectError (..)
  , MemberAlias
  , declaredPathText
  , firstDuplicate
  )
import Lara.Map.Wire (decodeMapManifestText)
import Lara.Prop (Prop)
import Lara.Replay (CheckInput, ReplayId, inputReplayId, inputUnit, replayArtifact, replayBackends)
import Lara.Source.Load
  ( LoadedSource
  , SourceCache
  , SourceLoadError (..)
  , canonicalPathKey
  , loadPolicyWith
  , loadSourceWith
  , loadedPolicy
  , loadedProgram
  , loadedPrepared
  , newSourceCache
  , readCachedFile
  , renderSourceLoadError
  )
import Lara.Wire (Outcome (..), verdictOutcome)

-- ---------------------------------------------------------------------------
-- The checked members
-- ---------------------------------------------------------------------------

-- | One member of a map, loaded from its current bytes and found acceptable on
-- its own and against the manifest.
--
-- __Opaque.__ See the module header: the constructor is the promise, so only
-- 'loadMap' may make one. The six observers are exactly what the qualification,
-- linking, and verdict stages need — deliberately not the whole
-- 'Lara.Elaborate.SourceResult', because a stage that could reach the member's
-- prune, diagnostics, or certificate report could reconstruct a decision this
-- module already made.
-- | The member's alias, the qualifier for every one of its local identities and
-- half of the @(alias, claim name)@ handle the map reports statuses under.
cmAlias :: CheckedMember -> MemberAlias
cmAlias (CheckedMember alias _ _ _ _ _) = alias

-- | The member's path __as the manifest spelled it__ — never the resolved
-- absolute path this module opened. This is the value the composite verdict
-- carries, which is why two runs from different directories agree byte for
-- byte.
cmDeclaredPath :: CheckedMember -> DeclaredPath
cmDeclaredPath (CheckedMember _ path _ _ _ _) = path

-- | The member's __own declared__ @artifact@ digest, read off its replay
-- identity and carried through unchanged. The map computes no digest of its
-- own: a map is a recheck, so the only identity it reports is the one the
-- member's author already wrote down.
cmArtifact :: CheckedMember -> Digest
cmArtifact (CheckedMember _ _ artifact _ _ _) = artifact

-- | The member's checked-boundary 'Unit': leaves, arguments, attacks, queries,
-- groups, signature, rules, contraries, exceptions, and theories. This is what
-- the linking stage qualifies and merges.
cmUnit :: CheckedMember -> Unit
cmUnit (CheckedMember _ _ _ unit _ _) = unit

-- | The member's replay identity: core version, policy id, selected backends,
-- and theory digests. The shared-contract check compares against it, and the
-- composite verdict's @policy@ and @backends@ sections are the manifest's own,
-- which every member has been shown to agree with.
cmReplayId :: CheckedMember -> ReplayId
cmReplayId (CheckedMember _ _ _ _ replayId _) = replayId

-- | The member's claims, __in declaration order__, each paired with its
-- normalized proposition.
--
-- This list cannot be recovered from 'cmUnit': a 'Lara.AST.Unit' records
-- @unitQueries@ as bare propositions and has lost the author's claim names. It
-- comes from the parsed 'Lara.AST.Program', and its order is what fixes the
-- composite verdict's @statuses@ ordering (member order, then that member's own
-- claim declaration order) as well as the reporting handle an alignment
-- coordinate names.
cmClaims :: CheckedMember -> [(PropId, Prop)]
cmClaims (CheckedMember _ _ _ _ _ claims) = claims

-- | A whole map's members, in manifest order, beside the manifest they came
-- from.
--
-- __Opaque__, for the same reason 'CheckedMember' is: the pairing is part of
-- the promise. The manifest travels along because the stages after this one
-- need its alignments, questions, policy id, and backend list, and re-reading
-- it would let them read a manifest this module never validated the members
-- against.
-- | The decoded manifest, exactly as it was read. Its @alignments@ and
-- @questions@ are unread by this module and pass through untouched.
checkedManifest :: CheckedMembers -> MapManifest
checkedManifest (CheckedMembers manifest _) = manifest

-- | The members, in manifest order — the order the composite verdict's
-- @members@, @nodes@, and @statuses@ sections are all keyed by.
-- Nonempty by type, inherited from 'Lara.Map.Types.mapMembers': the members are
-- a @traverse@ of the manifest's own list, so "a map with no members" is not a
-- state a later stage has to consider. 'Lara.Map.Link.linkMap' used to open with
-- an unreachable arm rejecting exactly that; the type is what removed it.
checkedMembers :: CheckedMembers -> NonEmpty CheckedMember
checkedMembers (CheckedMembers _ members) = members

-- ---------------------------------------------------------------------------
-- The load monad
-- ---------------------------------------------------------------------------

-- | @IO@ that short-circuits on the first 'MapError'.
--
-- Written out rather than pulled from @transformers@ — which ships with GHC but
-- is not a dependency of this package, and adding one for six lines is not a
-- trade worth making — and because the short-circuit /is/ the
-- diagnostic-precedence contract: only the first failure is reported, so a bind
-- that kept going would be a bug, not an option.
newtype MapLoad a = MapLoad {runMapLoad :: IO (Either MapError a)}

instance Functor MapLoad where
  fmap f (MapLoad m) = MapLoad (fmap (fmap f) m)

instance Applicative MapLoad where
  pure = MapLoad . pure . Right
  MapLoad mf <*> MapLoad ma = MapLoad $ do
    f <- mf
    case f of
      Left err -> pure (Left err)
      Right g -> fmap (fmap g) ma

instance Monad MapLoad where
  MapLoad m >>= k = MapLoad $ do
    result <- m
    case result of
      Left err -> pure (Left err)
      Right a -> runMapLoad (k a)

-- | Run an 'IO' action that cannot fail the map.
liftLoad :: IO a -> MapLoad a
liftLoad = MapLoad . fmap Right

-- | Stop with an ill-formed-map diagnostic (exit @2@).
boundary :: MapBoundaryError -> MapLoad a
boundary = MapLoad . pure . Left . MapBoundary

-- | Stop with a rejected-map diagnostic (exit @1@).
reject :: MapRejectError -> MapLoad a
reject = MapLoad . pure . Left . MapReject

-- ---------------------------------------------------------------------------
-- Loading a map's members
-- ---------------------------------------------------------------------------

-- | Read a @.laramap@ manifest and load every member it declares.
--
-- The stages run in the order the decision record fixes, and only the first
-- failure is reported:
--
--   1. read and decode the manifest — 'MBUnreadable', then 'MBWire'. An empty
--      @members@ section and a duplicate alias are settled by the /decoder/ and
--      arrive as 'MBWire'; this module has no constructor for either;
--   2. read the manifest's own policy file, the contract every member is
--      compared against — 'MBUnreadable', then 'MBManifestPolicySource', then
--      'MBManifestPolicyMismatch' when the manifest's declared policy id and
--      the file's disagree. None of the three is an 'MBWire': the manifest's
--      own bytes already decoded, and these are about a different file;
--   3. resolve the member paths and reject two aliases resolving to one file —
--      'MBDuplicatePath', in member order;
--   4. per member, in manifest order — 'MBUnreadable', then 'MBMemberSource',
--      then 'MBDuplicateClaim', then 'MRContract', then
--      'MRMemberAdmissionStop', then 'MRUnsupportedAdmission', then
--      'MRMemberRejected'.
--
-- Stage 4's order is the point of stage 4:
--
--   * a member's own source boundary runs before the map's contract check, so
--     an unreadable or unparseable member is never reported as a disagreement
--     with its peers;
--   * 'MBDuplicateClaim' sits between them, and above the contract check for
--     the same reason the source boundary is: a member whose claims cannot be
--     named unambiguously cannot be reported on at all, so there is nothing for
--     a contract disagreement to be said about;
--   * the contract check runs before both admission outcomes. A member can be
--     contract-mismatched /and/ quarantined at once, and the contract is the
--     more basic disagreement — an admission decision taken under a policy that
--     is not the map's contract says nothing about the map. This is why the
--     check is split in two ('sourceContractFailure' \/
--     'elaboratedContractFailure'): the fields that carry the meaning need only
--     the parsed source, so they can be decided before elaboration runs;
--   * the admission gate runs before any member is exported, so support a
--     policy prune removed can never reappear inside a linked unit.
--
-- 'MRContract' therefore appears at two points in the pipeline, and in practice
-- only the first can fire: @CFSignature@ and @CFTheories@ cannot fail unless
-- @CFPolicyStructure@ already has, which the first point has settled. See
-- 'elaboratedContractFailure' for why they are checked regardless.
loadMap :: FilePath -> IO (Either MapError CheckedMembers)
loadMap manifestPath = do
  -- One cache for the whole invocation: the manifest, its policy, every member,
  -- and every member's policy are read through it, so a file two of them name
  -- is read once and both see the same bytes.
  cache <- newSourceCache
  loadMapWith cache manifestPath

-- | 'loadMap' through a caller-owned cache, the map's counterpart of
-- 'Lara.Source.Load.loadSourceWith'.
--
-- The CLI never calls this: every @lara check \<map.laramap\>@ makes a fresh
-- cache through 'loadMap', and nothing in the production path shares one across
-- invocations, which is what keeps a map a recheck of current bytes (D1). It
-- exists for the one caller that needs the opposite: the map mode of
-- @scripts\/bench.hs@ (issue #319) warms a cache with one untimed pass, so that
-- its timed passes measure loading, checking and linking rather than disk
-- reads. A cache handed in here must not outlive the files it read; a caller
-- reusing one across edits would be reading stale bytes by construction.
loadMapWith :: SourceCache -> FilePath -> IO (Either MapError CheckedMembers)
loadMapWith cache manifestPath = runMapLoad $ do
  manifest <- readManifest cache manifestPath
  let baseDir = takeDirectory manifestPath
  contract <- readContractPolicy cache baseDir manifest
  resolved <- resolveMemberPaths baseDir (mapMembers manifest)
  members <- traverse (loadMember cache manifest contract) resolved
  pure (CheckedMembers manifest members)

-- | Stage 1: the manifest's own bytes.
readManifest :: SourceCache -> FilePath -> MapLoad MapManifest
readManifest cache path = do
  textOrError <- liftLoad (readCachedFile cache path)
  case textOrError of
    Left reason -> boundary (MBUnreadable path (show reason))
    Right text -> case decodeMapManifestText text of
      Left err -> boundary (MBWire err)
      Right manifest -> pure manifest

-- | Stage 2: the policy file the manifest names, parsed once.
--
-- This is the map's shared contract, and reading it is what makes the contract
-- check symmetric: no member is compared against a peer, and in particular not
-- against whichever member happened to load first. The manifest declares both
-- the policy id and the file, so the two must agree — a manifest naming
-- @agreement-v1@ beside a file that declares some other policy is ill-formed,
-- and is reported at the manifest's own boundary rather than as a disagreement
-- every member would then be blamed for.
--
-- __Nothing here is an 'MBWire'.__ The manifest's own bytes already decoded; a
-- failure at this stage is about a /different/ file. The three outcomes are
-- attributed accordingly: a path __this module__ resolved and could not open is
-- 'MBUnreadable' (which names that resolved path), a file it read and could not
-- parse is 'MBManifestPolicySource', and a file that parsed but declares
-- another policy is 'MBManifestPolicyMismatch'. Note the contrast with
-- 'readMemberSource': there, an unreadable /policy/ is the member's failure,
-- because the member's own @policy@ declaration chose the path. Here the
-- manifest chose it.
readContractPolicy :: SourceCache -> FilePath -> MapManifest -> MapLoad Policy
readContractPolicy cache baseDir manifest = do
  let path = baseDir </> declaredPathText (mapPolicyPath manifest)
  policyOrError <- liftLoad (loadPolicyWith cache path)
  case policyOrError of
    Left (PolicyUnreadable failed reason) -> boundary (MBUnreadable failed (show reason))
    Left err -> boundary (MBManifestPolicySource (renderSourceLoadError err))
    Right policy
      | policyId policy /= mapPolicy manifest ->
          boundary (MBManifestPolicyMismatch (mapPolicy manifest) (policyId policy))
      | otherwise -> pure policy

-- | Stage 3: resolve every member path against the manifest's directory, and
-- refuse two aliases that name one file.
--
-- Sameness is 'canonicalPathKey', the same identity the read cache uses, so a
-- symlink and its target, or a relative and an absolute spelling, are one file
-- to both. Only the loader can catch this: the codec deliberately never
-- resolves a path, so two spellings of one file are indistinguishable to it.
--
-- The reported path is the __canonical file the two share__, not either
-- member's spelling. With a symlink, or a relative path beside an absolute one,
-- the two aliases genuinely spell different things and no single manifest
-- spelling would be true of both; the resolved target is the one thing that is.
resolveMemberPaths
  :: FilePath -> NonEmpty MapMember -> MapLoad (NonEmpty (MapMember, FilePath))
resolveMemberPaths baseDir members = do
  entries <- liftLoad (traverse resolveOne members)
  case firstCollision Map.empty (NE.toList entries) of
    Just (earlier, later, shared) ->
      boundary (MBDuplicatePath (memberAlias earlier) (memberAlias later) shared)
    Nothing -> pure (fmap (\(member, path, _) -> (member, path)) entries)
  where
    resolveOne member = do
      -- @</>@ returns an absolute right-hand side unchanged, so this one line
      -- covers relative, parent-relative, and absolute declared paths.
      let path = baseDir </> declaredPathText (memberPath member)
      key <- canonicalPathKey path
      pure (member, path, key)

    firstCollision _ [] = Nothing
    firstCollision seen ((member, _, key) : rest) = case Map.lookup key seen of
      Just earlier -> Just (earlier, member, key)
      Nothing -> firstCollision (Map.insert key member seen) rest

-- ---------------------------------------------------------------------------
-- One member
-- ---------------------------------------------------------------------------

-- | Stage 4 for one member: load it through the ordinary source boundary, run
-- the ordinary source check, and clear all four gates before it becomes a
-- 'CheckedMember'.
--
-- Every step is the /same/ step @lara check@ takes on that file alone
-- ("Lara.Source.Load", 'Lara.Elaborate.prepareSource',
-- 'Lara.Elaborate.runSourceCheck'), so a member a map accepts is a member the
-- solo door accepts. Nothing is asserted and no trusted surface is widened:
-- this module reaches the member's elaborated unit only through
-- 'Lara.Elaborate.sourceResultCheckInput', the narrow checked-boundary export
-- that already existed.
loadMember
  :: SourceCache
  -> MapManifest
  -> Policy
  -> (MapMember, FilePath)
  -> MapLoad CheckedMember
loadMember cache manifest contract (member, path) = do
  source <- readMemberSource alias cache path
  -- The map's own well-formedness rule about the member, and it runs before the
  -- contract check for the reason every boundary stage does: a member whose
  -- claims cannot be named unambiguously cannot be reported on at all, so there
  -- is nothing for a contract disagreement to be said about. The @.lara@
  -- frontend does not guard this — 'Lara.Elaborate.prepareSource' refuses a
  -- repeated leaf, argument or group id and not a repeated claim id — so a
  -- member reaching here may genuinely carry one, and it is the map, whose
  -- reporting handle is @(alias, claim name)@, that has to refuse it.
  case firstDuplicate (map fst (memberClaims (loadedProgram source))) of
    Just claim -> boundary (MBDuplicateClaim alias claim)
    Nothing -> pure ()
  -- The contract fields that need only the PARSED source, run before anything
  -- that can stop on admission. This ordering is the whole reason the check is
  -- split: a member can be simultaneously contract-mismatched and
  -- policy-quarantined (its own policy copy carrying an @admission@ row the
  -- manifest's copy lacks is exactly both at once), and the documented
  -- precedence says such a member reports 'MRContract'. Deciding these three
  -- fields here makes that true rather than documenting an exception to it —
  -- and it is the right answer on the merits, because an admission stop under a
  -- policy that is not the map's contract would name a policy the map does not
  -- use.
  case sourceContractFailure manifest contract source of
    Just field -> reject (MRContract alias field)
    Nothing -> pure ()
  input <- case loadedPrepared source of
    -- The policy's admission table classed a leaf @reject@, so elaboration
    -- never produced a unit and there is nothing to compare or to link. This is
    -- 'MRMemberAdmissionStop' and not 'MRMemberRejected' because the latter
    -- carries a 'Lara.AST.Rejection' and a §4.3 admission stop has no rejection
    -- class; and not 'MRUnsupportedAdmission' because this member genuinely
    -- fails the policy rather than merely needing a feature v1 declined to
    -- ship. See both constructors' notes in "Lara.Map.Types".
    SourceRejected rejection -> reject (MRMemberAdmissionStop alias (renderAdmissionRejection rejection))
    SourceAccepted prepared -> pure prepared
  let result = runSourceCheck input
      audit = sourceResultAudit result
  checkInput <- case sourceResultCheckInput result of
    -- A policy quarantine, which makes the audit nonempty, so the gate below
    -- would refuse this member with the identical rendered audit. Taking the
    -- arm here is what lets the gate be written as a total case rather than a
    -- partial pattern; the contract fields that must outrank it have already
    -- been decided above.
    Left quarantined -> reject (MRUnsupportedAdmission alias (renderAdmissionAudit quarantined))
    Right checked -> pure checked
  case elaboratedContractFailure contract source checkInput of
    Just field -> reject (MRContract alias field)
    Nothing -> pure ()
  -- The admission gate, and it runs BEFORE anything linkable is exported: a
  -- member whose audit is nonempty had support pruned, and a map that admitted
  -- it would silently resurrect that support inside the linked unit. This is
  -- also what makes @evidence-blocked@ unreachable in a composite verdict.
  if admissionAuditIsEmpty audit
    then pure ()
    else reject (MRUnsupportedAdmission alias (renderAdmissionAudit audit))
  case verdictOutcome (sourceResultVerdict result) of
    Reject rejection -> reject (MRMemberRejected alias rejection)
    Accept{} -> pure ()
  pure
    ( CheckedMember
        alias
        (memberPath member)
        (replayArtifact (inputReplayId checkInput))
        (inputUnit checkInput)
        (inputReplayId checkInput)
        (memberClaims (loadedProgram source))
    )
  where
    alias = memberAlias member

-- | Load one member's program and policy, splitting the map's own boundary from
-- the member's.
--
-- The split is __who chose the path__, not who opened the file:
--
--   * the member's __artifact__ path came from the manifest and was resolved by
--     this module, so failing to open it is the map's own failure —
--     'MBUnreadable', naming the resolved path the operator must go look at;
--   * everything else is the __member's__ source boundary — 'MBMemberSource',
--     carrying the member's own exit-@2@ text under the member's alias. That
--     includes its __policy__ file, whose path this module never chose: it
--     comes from the member's own @policy@ declaration through
--     'Lara.Source.Load.resolvePolicyPath'. An operator told "member @paper_a@:
--     cannot read policy …" knows to open @paper_a@; the same words under the
--     map's own boundary would send them to the manifest, which has nothing to
--     do with it.
--
-- Both exit @2@; the split decides which diagnostic is readable, never which
-- inputs are accepted.
readMemberSource :: MemberAlias -> SourceCache -> FilePath -> MapLoad LoadedSource
readMemberSource alias cache path = do
  loaded <- liftLoad (loadSourceWith cache path)
  case loaded of
    Left (SourceUnreadable failed reason) -> boundary (MBUnreadable failed (show reason))
    Left err -> boundary (MBMemberSource alias (renderSourceLoadError err))
    Right source -> pure source

-- | The member's claims, in declaration order, paired with their propositions.
--
-- Duplicate names are /not/ filtered here: 'loadMember' refuses the member
-- outright ('MBDuplicateClaim'). Silently deduplicating would be worse than
-- either, because the two rows may carry different propositions and dropping
-- one would report a status for a claim the author did not write.
memberClaims :: Program -> [(PropId, Prop)]
memberClaims program = [(claimId claim, claimFormal claim) | DeclClaim claim <- programDecls program]

-- ---------------------------------------------------------------------------
-- The shared contract
-- ---------------------------------------------------------------------------

-- | The half of the shared contract decidable from the __parsed source alone__,
-- before elaboration and therefore before any admission decision.
--
-- Three of the five fields live here, and they are the three that carry the
-- meaning. What is compared is __structures, never names__:
--
-- [@CFPolicyId@] the member's declared policy id against the manifest's.
--
-- [@CFPolicyStructure@] the member's /parsed/ 'Lara.AST.Policy' against the
--   manifest's. Comments and whitespace are gone after parsing, so this accepts
--   two policy files that differ only in formatting, and rejects a
--   redefinition hiding under a shared policy id — which comparing ids alone
--   would wave through. This is the load-bearing field: a map whose members
--   silently ran under different rules would produce a composite verdict that
--   means nothing.
--
-- [@CFBackends@] @'sort' ('programBackends' prog)@ against the manifest list.
--   The comparison is __sorted, and that asymmetry is deliberate — do not
--   \"fix\" it to a positional one.__ The manifest is required to be
--   canonically ascending and duplicate-free, because that is what makes
--   manifest /bytes/ canonical; a member is under no such rule, and
--   'Lara.Elaborate' passes a program's backend list through in author
--   declaration order. A member written @use backends [ra\@1, nd\@1]@ would
--   therefore be unsatisfiable under a positional test — it could never join
--   any map — for a difference that carries no meaning, since backend selection
--   is a set.
--
-- The fields are tested in that order, which is 'ContractField' order except
-- that @CFBackends@ is decided ahead of @CFSignature@ and @CFTheories@. That
-- reordering is unobservable: those two cannot fail unless @CFPolicyStructure@
-- already has (see 'elaboratedContractFailure'), so no member can reach a state
-- where the two orders disagree.
sourceContractFailure :: MapManifest -> Policy -> LoadedSource -> Maybe ContractField
sourceContractFailure manifest contract source
  | programPolicy program /= mapPolicy manifest = Just CFPolicyId
  | loadedPolicy source /= contract = Just CFPolicyStructure
  | sort (programBackends program) /= mapBackends manifest = Just CFBackends
  | otherwise = Nothing
  where
    program = loadedProgram source

-- | The half of the shared contract that needs the __elaborated__ unit, run
-- after the member's source check.
--
-- Stated plainly: with today's elaborator neither field can fail on its own.
-- @unitSigma@ and @unitTheories@ are copied verbatim from the policy
-- (@src\/Lara\/Elaborate\/Internal.hs@), and 'sourceContractFailure' has
-- already compared the whole parsed policy, so a member reaching here agrees on
-- both by construction. They are checked anyway, and on the elaborated unit
-- rather than on the policy, because the unit is the object the linking stage
-- merges: if a later elaborator ever derived either field instead of copying
-- it, this is the check that would notice, and the alternative — trusting that
-- the copy stays a copy — is a review-time promise rather than a
-- machine-checked one.
--
-- The @CFBackends@ line is the same kind of guard, and it is what makes moving
-- that field onto 'programBackends' provably not a semantic change:
-- 'Lara.Elaborate' hands @programBackends@ straight to @mkReplayId@, so the two
-- lists are the same list, and this asserts it on every member rather than
-- leaving it to a comment. It cannot fire today.
elaboratedContractFailure :: Policy -> LoadedSource -> CheckInput -> Maybe ContractField
elaboratedContractFailure contract source checkInput
  | unitSigma unit /= policySigma contract = Just CFSignature
  | unitTheories unit /= policyTheories contract = Just CFTheories
  | sort (replayBackends (inputReplayId checkInput))
      /= sort (programBackends (loadedProgram source)) =
      Just CFBackends
  | otherwise = Nothing
  where
    unit = inputUnit checkInput
