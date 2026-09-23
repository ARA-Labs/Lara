{-# LANGUAGE DerivingVia #-}

-- | Stage five of the multi-artifact map: resolve the manifest's coordinates,
-- check the linked unit, evaluate the declared alignments, and report one
-- composite verdict.
--
-- == Position in the pipeline
--
-- @
-- .laramap bytes -> decode  ("Lara.Map.Wire")
--                -> load and recheck each member  ("Lara.Map.Load")
--                -> qualify + merge + saturate + check  ("Lara.Map.Link")
--                -> resolve coordinates, evaluate alignments, compose   <- here
--                -> @map-verdict\@1@ bytes  ("Lara.Map.Wire")
-- @
--
-- 'runMap' is the whole @.laramap@ operation and is what @lara check@'s third
-- door calls. 'checkMap' is its pure half, so the CLI shell owns nothing but
-- the @stderr@ channel and the exit code — the same division @app/Main.hs@
-- already has for the @.lara@ and @.sexp@ doors.
--
-- == The two stages this module owns
--
-- "Lara.Map.Load" deliberately stopped short of /reference resolution/, and
-- "Lara.Map.Link" of /alignment evaluation/, because both consume the same
-- coordinates: an alignment and a question both name @(member alias, claim
-- name, coordinate)@ triples, and the claim list they resolve against is
-- exactly what 'Lara.Map.Load.cmClaims' hands onward. They land together here.
--
--   * __resolution__ turns each coordinate into the value it names, and is a
--     /boundary/ stage: an undeclared alias, an undeclared claim, an argument
--     index past the claim's arity, and a question whose references mix a
--     whole-claim selector with an argument selector are all ill-formed maps
--     (exit 2). Nothing is decided about the members by resolving.
--   * __evaluation__ decides each alignment's assertion against the resolved
--     values, and is a /rejection/ stage: a false alignment is
--     'Lara.Map.Types.MRAlignmentFalse' (exit 1). An alignment is __checked,
--     never applied__ — the map does not rewrite a member's propositions to
--     make an assertion come true, which is why symbol substitution and
--     ontology mapping have no syntax (decision record D6).
--
-- The two are separated in the pipeline by /linking/, and that order is the
-- decision record's precedence (D11 stages 5, 6, 7), not an accident of
-- implementation. Both of this module's own boundary decisions are taken
-- before either of its rejections, so no map is reported as rejected when this
-- module could also have called it ill-formed; and among the rejections a link
-- failure outranks a false alignment, because a map whose linked unit does not
-- check has no composite result for an alignment to be reported beside.
--
-- That is a statement about /this stage/, and deliberately not about the whole
-- pipeline. "Lara.Map.Load" interleaves its own boundary and rejection stages
-- per member, so a map with an unreadable member and a contract-mismatched one
-- can still exit 1: the decision record's rule is that a boundary stage
-- precedes a reject stage wherever both /could fire on the same subject/, not
-- that every boundary failure anywhere outranks every rejection.
--
-- == The cross-driver parity envelope
--
-- @map-check-input\@1@ is a __parity anchor__, not a user-facing artifact
-- format and not a snapshot: 'runMap' never reads one, and the production path
-- from a @.laramap@ to a verdict does not pass through these bytes. It exists
-- so that @lean\/Lara\/Map\/Driver.lean@ — which has no @.lara@ parser and no
-- filesystem story — can be handed the same checked-boundary material the
-- Haskell frontend linked, reconstruct the linking itself, and have its
-- verdict byte-compared against this one. That is why it carries elaborated
-- 'Lara.AST.Unit's rather than paths.
--
-- Each member's @UNIT@ is exactly 'Lara.Wire.encodeUnit''s existing form, so
-- the Lean driver's existing @decodeUnit@ consumes it unchanged and no frozen
-- byte moves. The @claims@ section is the one thing a 'Lara.AST.Unit' cannot
-- supply: @unitQueries@ is a bare @['Lara.Prop.Prop']@ and has lost the
-- author's claim names, and @(alias, claim name)@ is the map's reporting
-- handle and the coordinate an alignment names.
--
-- __The envelope has its own tag table__, rather than growing
-- "Lara.Map.Wire"'s 'Lara.Map.Wire.MapTag'. This is the same ruling the
-- decision record already made one level down, for the same reason: @MapTag@
-- spells the two /frozen/ map grammars, the manifest and the composite
-- verdict, and a debugging aid for two implementations must be free to move
-- without perturbing them. The tables overlap on spellings deliberately — the
-- envelope names the same concepts with the same words — and each carries its
-- own collision-freedom property.
--
-- == What a decoded envelope has been checked for
--
-- 'decodeMapCheckInput' is the counterpart of 'Lara.Map.Wire.decodeMapVerdict':
-- an envelope is __terminal input__ for the driver that reads it, so its
-- decoder settles everything its own bytes determine — nonempty members with
-- unique aliases, ascending duplicate-free backends, per-member claim-name
-- uniqueness, agreement of every member's unit with the first on the shared
-- policy sections, and alignment coordinates that resolve. What it does
-- __not__ do is turn the result back into a 'Lara.Map.Load.CheckedMembers':
-- that type is a promise about files on disk that were read and rechecked, and
-- no byte string can make that promise. 'MapCheckInput' is therefore ordinary
-- derived data, decodable for round-trip testing and for the parity harness,
-- and never a way back into the production path.
module Lara.Map.Driver
  ( -- * The @.laramap@ operation
    runMap
  , checkMap
    -- * The two stages between loading and the verdict
  , AlignmentTargets (..)
  , ResolvedAlignment (..)
  , resolveReferences
  , evaluateAlignments
    -- * The cross-driver parity envelope
  , MapCheckInput
  , mkMapCheckInput
  , mciPolicy
  , mciBackends
  , mciMembers
  , mciAlignments
  , MapCheckMember (..)
  , mapCheckInput
  , encodeMapCheckInput
  , decodeMapCheckInput
  , decodeMapCheckInputText
    -- * The envelope's own tag vocabulary
  , EnvTag (..)
  , envTagToString
  , parseEnvTag
  ) where

-- @foldl'@ through a qualified name on purpose. A plain
-- @import Data.List (foldl')@ is *required* on GHC 9.6, which CI pins, because
-- base 4.18's Prelude does not export it — and is flagged redundant on GHC
-- 9.10, where base 4.20's Prelude does. A qualified import is clean on both:
-- removing it makes @List.foldl'@ unresolvable, so it is never redundant, and
-- no CPP is needed to say so.
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map

import Lara.AST
  ( BackendId (..)
  , Digest (..)
  , LeafId (..)
  , PolicyId (..)
  , PropId (..)
  , Unit (..)
  )
import Lara.Map.Link
  ( LinkedMap
  , linkMap
  , lmEdges
  , lmLabels
  , lmNodes
  , lmStatuses
  )
import Lara.Map.Load
  ( CheckedMember
  , CheckedMembers
  , checkedManifest
  , checkedMembers
  , cmAlias
  , cmArtifact
  , cmClaims
  , cmDeclaredPath
  , cmUnit
  , loadMap
  )
import Lara.Map.Types
import Lara.Prop (Prop (..), Term, nfTerm, (===))
import Lara.Replay (CoreVersion (..))
import Lara.Strict (SExpr (..))
import Lara.Map.Wire (decodeAlignmentIn, encodeAlignment)
import Lara.Wire
  ( ParseError (..)
  , WireError (..)
  , decodeAtomSExpr
  , decodeUnit
  , encodeAtom
  , encodeUnit
  , parseSExpr
  )

-- ---------------------------------------------------------------------------
-- The .laramap operation
-- ---------------------------------------------------------------------------

-- | Read a @.laramap@ manifest, load and recheck its members, resolve its
-- coordinates, link and check the map, evaluate its alignments, and report the
-- composite verdict.
--
-- Every filesystem access a map performs happens inside 'loadMap'; everything
-- after it is pure. A failure is the __first__ one the decision record's
-- precedence reaches, and 'Lara.Map.Types.mapErrorExitCode' turns it into the
-- 2-or-1 the CLI exits with.
runMap :: FilePath -> IO (Either MapError MapVerdict)
runMap manifestPath = do
  loaded <- loadMap manifestPath
  pure (loaded >>= checkMap)

-- | The pure half of 'runMap': everything from loaded members to a composite
-- verdict.
--
-- Exported so that the CLI is a thin shell over it and so that the stages can
-- be driven from a test without a filesystem. The three steps are the decision
-- record's stages 5, 6 and 7, in that order.
checkMap :: CheckedMembers -> Either MapError MapVerdict
checkMap loaded = do
  resolved <- resolveReferences loaded
  linked <- linkMap loaded
  evaluateAlignments resolved
  pure (composeVerdict loaded linked)

-- | Assemble the composite verdict from the manifest's identity, the members'
-- own declared identities, and the linked map's grounded result.
--
-- Nothing is computed here: every section is carried from something that
-- already decided it, which is what makes the deterministic ordering
-- ("Lara.Map.Link" for @nodes@, @labels@, @edges@ and @statuses@;
-- "Lara.Map.Load" for @members@) observable in the bytes rather than imposed
-- by the encoder.
composeVerdict :: CheckedMembers -> LinkedMap -> MapVerdict
composeVerdict loaded linked =
  MapVerdict
    { mvScope = ScopeMap
    , mvSchema = MapVerdictSchemaV1
    , mvCore = LaraCoreV02
    , mvPolicy = mapPolicy manifest
    , mvBackends = mapBackends manifest
    , mvMembers =
        fmap
          ( \member ->
              MemberRecord
                { mrAlias = cmAlias member
                , mrPath = cmDeclaredPath member
                , mrArtifact = cmArtifact member
                }
          )
          (checkedMembers loaded)
    , mvNodes = lmNodes linked
    , mvLabels = lmLabels linked
    , mvEdges = lmEdges linked
    , mvStatuses = lmStatuses linked
    }
  where
    manifest = checkedManifest loaded

-- ---------------------------------------------------------------------------
-- Reference resolution
-- ---------------------------------------------------------------------------

-- | The two values one alignment compares.
--
-- A closed sum with no mixed constructor, so \"the two coordinates select the
-- same kind of target\" is a property of the /type/ rather than a rule a later
-- reader has to remember. The manifest decoder already refuses a mixed pair
-- inside an alignment; this makes the refusal structural on the way out too.
data AlignmentTargets
  = -- | both coordinates are @whole@: the claims' propositions
    WholeTargets Prop Prop
  | -- | both coordinates are @(arg n)@: the selected argument terms
    ArgTargets Term Term
  deriving (Eq, Show)

-- | Resolve every coordinate the manifest declares, in manifest order:
-- alignments first, then questions.
--
-- The result is one 'AlignmentTargets' per alignment, in manifest order, which
-- is what fixes the position 'MRAlignmentFalse' reports. A question resolves
-- for validation only and contributes nothing: a map question is presentation,
-- naming what the map is /for/, and carries no checker obligation.
--
-- Every failure here is a __boundary__ failure (exit 2). Resolution decides
-- nothing about the members; it only asks whether the manifest's coordinates
-- name anything at all.
resolveReferences :: CheckedMembers -> Either MapError [ResolvedAlignment]
resolveReferences loaded = do
  targets <- traverse alignmentTargets (mapAlignments manifest)
  mapM_ questionTargets (mapQuestions manifest)
  pure
    [ ResolvedAlignment
        { raPosition = position
        , raAlignment = alignment
        , raTargets = target
        }
    | (position, alignment, target) <-
        zip3 [0 ..] (mapAlignments manifest) targets
    ]
  where
    manifest = checkedManifest loaded

    -- One claim table per member, keyed by alias. Built once: a manifest may
    -- name one member's claims many times.
    claims :: Map.Map MemberAlias [(PropId, Prop)]
    claims =
      Map.fromList
        [(cmAlias member, cmClaims member) | member <- NE.toList (checkedMembers loaded)]

    -- 'pairTargets' can report a mixed selector, and for an /alignment/ that
    -- arm is unreachable: the manifest decoder already refuses a pair mixing
    -- 'CoordWhole' with @'CoordArg' n@. It is shared with the question path
    -- rather than special-cased away, because the question path is where the
    -- condition is live and a second spelling of one check is a second thing
    -- to keep in step.
    alignmentTargets alignment = do
      left <- resolveRef claims (alignLeft alignment)
      right <- resolveRef claims (alignRight alignment)
      pairTargets (refAlias (alignLeft alignment)) (refAlias (alignRight alignment)) left right

    -- A question's reference list is heterogeneous by construction: the
    -- grammar admits any number of references with any selectors, so unlike an
    -- alignment's pair, nothing has yet refused a list that mixes them. The
    -- decision record puts that check here for exactly that reason. Each
    -- reference is resolved first, in declaration order, so a question naming
    -- an undeclared claim reports that rather than a selector complaint about
    -- a coordinate that does not exist.
    questionTargets question = do
      resolved <-
        traverse
          (\ref -> (,) (refAlias ref) <$> resolveRef claims ref)
          (mapQuestionRefs question)
      case resolved of
        -- Unreachable: the manifest decoder refuses a question relating fewer
        -- than two references. Written out rather than defaulted, because the
        -- alternative is a partial pattern.
        [] -> Right ()
        ((firstAlias, firstValue) : rest) ->
          -- Every later reference is compared against the FIRST, so the
          -- diagnostic names the reference that set the kind and the first one
          -- that broke it, rather than an adjacent pair that happens to differ.
          mapM_
            (\(alias, value) -> pairTargets firstAlias alias firstValue value)
            rest

-- | One resolved coordinate: the value the reference names.
data Selected
  = SelectedWhole Prop
  | SelectedArg Term

-- | Resolve one coordinate against the members' claim tables.
--
-- The three failures are in the decision record's order — the alias first,
-- because a reference to an undeclared member says nothing about a claim; then
-- the claim; then the argument index against the claim's own arity.
resolveRef :: Map.Map MemberAlias [(PropId, Prop)] -> MapRef -> Either MapError Selected
resolveRef claims ref = do
  memberClaims <- case Map.lookup (refAlias ref) claims of
    Nothing -> Left (MapBoundary (MBUnknownAlias (refAlias ref)))
    Just declared -> Right declared
  proposition <- case lookup (refClaim ref) memberClaims of
    Nothing -> Left (MapBoundary (MBUnknownClaim (refAlias ref) (refClaim ref)))
    Just p -> Right p
  case refCoord ref of
    CoordWhole -> Right (SelectedWhole proposition)
    CoordArg index ->
      let Prop _ arguments = proposition
          position = argIndexInt index
       in if position < length arguments
            then Right (SelectedArg (arguments !! position))
            else
              Left
                ( MapBoundary
                    ( MBCoordinateOutOfRange
                        (refAlias ref)
                        (refClaim ref)
                        index
                        (length arguments)
                    )
                )

-- | Pair two resolved coordinates, refusing a mix of selector kinds.
--
-- The aliases are carried only for the diagnostic: 'MBMixedSelector' names the
-- two references' members, which is what an operator needs to find the two
-- lines of the manifest that disagree.
pairTargets
  :: MemberAlias -> MemberAlias -> Selected -> Selected -> Either MapError AlignmentTargets
pairTargets leftAlias rightAlias left right = case (left, right) of
  (SelectedWhole p, SelectedWhole q) -> Right (WholeTargets p q)
  (SelectedArg s, SelectedArg t) -> Right (ArgTargets s t)
  _ -> Left (MapBoundary (MBMixedSelector leftAlias rightAlias))

-- ---------------------------------------------------------------------------
-- Alignment evaluation
-- ---------------------------------------------------------------------------

-- | The one alignment, its manifest position, and what its two coordinates
-- resolved to.
--
-- __The pairing is the type.__ 'evaluateAlignments' used to take two parallel
-- lists and @zip3@ them against @[0 ..]@. That is silent truncation with a bad
-- failure mode: a @targets@ list shorter than @alignments@ drops the tail, every
-- dropped alignment is treated as holding, and the map /accepts/. It was safe
-- only because the single in-tree caller derived both lists from one manifest in
-- the same 'traverse' — a convention held in place by a comment, on two exported
-- functions any test or future caller could pair up differently. In a
-- verdict-producing pipeline the cost of getting it wrong is silent acceptance,
-- which is the one outcome that must not be reachable by accident.
data ResolvedAlignment = ResolvedAlignment
  { -- | position in the manifest's @alignments@ section, 0-based; the number a
    -- rejection reports
    raPosition :: Int
  , raAlignment :: Alignment
  , raTargets :: AlignmentTargets
  }
  deriving (Eq, Show)

-- | Decide every declared alignment against the coordinates it names, and
-- report the __lowest-numbered__ one that does not hold.
--
-- An alignment is a claim /about/ the members, evaluated against them; it is
-- never a rewrite that makes them agree. A false assertion is a map rejection
-- (exit 1), not a warning and not a repair — see D6. The position reported is
-- the alignment's own position in the manifest, carried on the
-- 'ResolvedAlignment' rather than recovered by counting.
--
-- __Identity is @≡@, not structural equality__, and on both arms. A whole
-- coordinate compares propositions with 'Lara.Prop.(===)', the trusted
-- identity relation the checker itself uses for @supports@ and for contrary
-- matching; an argument coordinate compares terms by their normal forms, which
-- is the same relation one level down. Comparing raw syntax instead would make
-- an alignment turn on a numeric literal's spelling, and would let a map
-- reject two members the checker considers to be saying the same thing.
evaluateAlignments :: [ResolvedAlignment] -> Either MapError ()
evaluateAlignments resolved =
  case [ (raPosition r, alignAssertion (raAlignment r))
       | r <- resolved
       , not (holds (alignAssertion (raAlignment r)) (raTargets r))
       ] of
    [] -> Right ()
    ((position, assertion) : _) -> Left (MapReject (MRAlignmentFalse position assertion))
  where
    holds assertion target =
      case assertion of
        Same -> identical target
        Different -> not (identical target)

    identical target = case target of
      WholeTargets p q -> p === q
      ArgTargets s t -> nfTerm s == nfTerm t

-- ---------------------------------------------------------------------------
-- The cross-driver parity envelope
-- ---------------------------------------------------------------------------

-- | One member as the parity envelope carries it: its reporting identity, its
-- claim names paired with their propositions, and its elaborated unit.
--
-- The path is the __manifest-spelled__ 'DeclaredPath', for the same reason the
-- composite verdict carries that one: two people running one manifest from
-- different directories must produce the same envelope bytes, and a resolved
-- absolute path would make them differ.
data MapCheckMember = MapCheckMember
  { mcmAlias :: MemberAlias
  , mcmPath :: DeclaredPath
  , mcmArtifact :: Digest
  , -- | in the member's own claim declaration order, which is what fixes the
    -- composite verdict's @statuses@ ordering
    mcmClaims :: [(PropId, Prop)]
  , mcmUnit :: Unit
  }
  deriving (Eq, Show)

-- | A whole map at its checked boundary: the shared contract's identity, the
-- members, and the alignments still to be decided.
--
-- The manifest's @questions@ are deliberately absent. They are presentation —
-- they carry no checker obligation and no verdict section — so a driver reading
-- this envelope has nothing to do with them, and carrying them would invite a
-- second implementation of a check that decides nothing.
-- __The constructor is hidden__, for the reason 'Lara.Map.Types.MapManifest'\'s
-- is: this is decode-boundary data whose fields carry invariants the rest of
-- the pipeline reads as a promise, and it is the whole basis of the
-- cross-driver parity claim — an envelope this side can forge but the Lean
-- decoder would refuse is a divergence manufactured here. Build one with
-- 'mkMapCheckInput', or with 'mapCheckInput' from loaded members;
-- 'decodeMapCheckInput' routes through the former. The field selectors are
-- exported, so a test can still take a valid envelope apart and put a defect
-- back — the same shape 'Lara.Replay.CheckInput' uses behind @mkCheckInput@.
data MapCheckInput = MapCheckInput
  { mciPolicy :: PolicyId
  , -- | @(id, version)@ pairs, duplicate-free and ascending, exactly as the
    -- manifest carries them
    mciBackends :: [(BackendId, String)]
  , -- | aliases unique, in manifest order; nonemptiness is the type's
    mciMembers :: NonEmpty MapCheckMember
  , mciAlignments :: [Alignment]
  }
  deriving (Eq, Show)

-- | Build an envelope, or say which documented invariant the fields break.
--
-- The sanctioned constructor. Each check reproduces the decoder's own context
-- and message verbatim, so an envelope built here and one decoded from bytes
-- fail identically, and 'decodeMapCheckInput' calls this rather than assembling
-- the record itself — which is what keeps the two from drifting.
--
-- Checks run in the envelope's own section order (backends, members,
-- alignments), matching the decoder, which stops at the first section that
-- fails. Alignment resolvability — does this alias exist, does it declare
-- this claim, is the coordinate in range — is checked here too, because it
-- is a fact about the members this envelope carries rather than about the bytes
-- it was read from.
mkMapCheckInput
  :: PolicyId
  -> [(BackendId, String)]
  -> NonEmpty MapCheckMember
  -> [Alignment]
  -> Either MapWireError MapCheckInput
mkMapCheckInput policy backends members alignments =
  runEnvDecode $ do
    if strictlyAscending backends
      then eok ()
      else
        ewerr
          "map check-input backends"
          "backends must be duplicate-free and ascending by (id, version)"
    case firstDuplicate (map mcmAlias (NE.toList members)) of
      Just duplicate ->
        ewerr
          "map check-input members"
          ("duplicate member alias " ++ aliasText duplicate)
      Nothing -> eok ()
    sharedSectionsAgree members
    mapM_ (resolvableAlignment members) alignments
    mapM_ sameKind alignments
    eok
      MapCheckInput
        { mciPolicy = policy
        , mciBackends = backends
        , mciMembers = members
        , mciAlignments = alignments
        }
  where
    sameKind alignment =
      case (refCoord (alignLeft alignment), refCoord (alignRight alignment)) of
        (CoordWhole, CoordWhole) -> eok ()
        (CoordArg _, CoordArg _) -> eok ()
        _ ->
          ewerr
            "map check-input alignment"
            "an alignment's two coordinates must both be whole or both be (arg n)"

-- | Project the loaded members onto the parity envelope.
--
-- A projection of what 'loadMap' produced: the envelope adds nothing and
-- decides nothing, which is what makes it an anchor rather than a second
-- source of truth. In particular the @artifact@ digest is the member's own
-- declared identity, carried through unchanged.
--
-- __Why this returns 'Either'.__ Loading settles the members and the shared
-- contract, but not the alignments: an alignment naming an alias no member
-- declares, or a coordinate past an argument's arity, survives 'loadMap' and is
-- caught later by 'resolveReferences'. This projection used to be total and its
-- one caller guarded it by remembering to run 'resolveReferences' first — a
-- convention, not a type. Routing through 'mkMapCheckInput' makes the guard
-- structural, so no future caller can emit an envelope the Lean decoder would
-- refuse. Callers that have already resolved see 'Right' every time.
mapCheckInput :: CheckedMembers -> Either MapWireError MapCheckInput
mapCheckInput loaded =
  mkMapCheckInput
    (mapPolicy manifest)
    (mapBackends manifest)
    (fmap memberInput (checkedMembers loaded))
    (mapAlignments manifest)
  where
    manifest = checkedManifest loaded

    memberInput :: CheckedMember -> MapCheckMember
    memberInput member =
      MapCheckMember
        { mcmAlias = cmAlias member
        , mcmPath = cmDeclaredPath member
        , mcmArtifact = cmArtifact member
        , mcmClaims = cmClaims member
        , mcmUnit = cmUnit member
        }

-- ---------------------------------------------------------------------------
-- The envelope's own tag vocabulary
-- ---------------------------------------------------------------------------

-- | Every keyword this grammar __owns__, as a closed sum type.
--
-- Its own table, deliberately disjoint from 'Lara.Map.Wire.MapTag' as a /type/;
-- the module header says why the two must not be merged. The concrete spellings
-- live in exactly one place ('envTagToString'), and 'parseEnvTag' derives its
-- reverse lookup from that function by enumerating the type.
--
-- __What is no longer here.__ The eleven keywords of the @alignment@ production
-- — @alignment@, @ref@, @whole@, @arg@, @same@, @different@, @author@,
-- @audit-status@, @rationale@ and the two remaining audit statuses — used to be
-- listed here as well, spelled identically to their 'Lara.Map.Wire.MapTag'
-- counterparts, with a within-table collision test on each table and nothing
-- asserting the two agreed. That is not two grammars reusing a word, which the
-- split exists for; it is two grammars sharing a whole production, and CLAUDE.md
-- asks for one spelling table per vocabulary. The production now has exactly one
-- codec ('Lara.Map.Wire.decodeAlignmentIn'), so the envelope cannot keep an old
-- spelling after the manifest moves — which would leave the Lean parity harness
-- comparing against a production the manifest no longer emits. @ETAlignments@
-- stays, because the /section wrapper/ is this envelope's own.
data EnvTag
  = -- envelope
    ETMapCheckInput1
  | ETPolicy
  | ETBackends
  | ETBackend
  | ETMembers
  | ETMember
  | ETArtifact
  | ETClaims
  | ETClaim
  | -- the alignments SECTION; its contents are Lara.Map.Wire's production
    ETAlignments
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The on-the-wire spelling of an envelope keyword.
envTagToString :: EnvTag -> String
envTagToString t = case t of
  ETMapCheckInput1 -> "map-check-input@1"
  ETPolicy -> "policy"
  ETBackends -> "backends"
  ETBackend -> "backend"
  ETMembers -> "members"
  ETMember -> "member"
  ETArtifact -> "artifact"
  ETClaims -> "claims"
  ETClaim -> "claim"
  ETAlignments -> "alignments"

{-# NOINLINE envTagTable #-}
envTagTable :: Map.Map String EnvTag
envTagTable = Map.fromList [(envTagToString t, t) | t <- [minBound .. maxBound]]

-- | Parse an envelope keyword, inverse to 'envTagToString'. The table is
-- derived from 'envTagToString' by enumerating 'EnvTag', so a spelling
-- collision would break that inverse silently (@Map.fromList@ keeps one value
-- per key); @prop_envTagTableTotal@ (MapSpec) rejects collisions.
parseEnvTag :: String -> Maybe EnvTag
parseEnvTag s = Map.lookup s envTagTable

-- ---------------------------------------------------------------------------
-- The envelope codec
-- ---------------------------------------------------------------------------

-- | The envelope decoder monad: 'Either' 'MapWireError' with a 'MonadFail'
-- instance, so an arity-checked field list can be destructured directly in a
-- @do@ block. The failure path is unreachable — 'matchEnv' verifies arity
-- before the pattern binds. Mirrors "Lara.Map.Wire"'s @MapDecode@ exactly.
newtype EnvDecode a = EnvDecode {runEnvDecode :: Either MapWireError a}
  deriving (Functor, Applicative, Monad) via Either MapWireError

instance MonadFail EnvDecode where
  fail = ewerr "decode"

ewerr :: String -> String -> EnvDecode a
ewerr context message = EnvDecode (Left (MapWireError context message))

-- | Lift a smart constructor's already-located rejection.
efail :: MapWireError -> EnvDecode a
efail = EnvDecode . Left

eok :: a -> EnvDecode a
eok = EnvDecode . Right

-- | Lift a smart constructor's rejection into a located codec error.
erequired :: String -> String -> Maybe a -> EnvDecode a
erequired context message = maybe (ewerr context message) eok

-- | Build a tagged list: @(tag e1 … en)@.
etagged :: EnvTag -> [SExpr] -> SExpr
etagged t es = SList (SAtom (envTagToString t) : es)

-- | Match a tagged list with exactly @n@ payload fields.
matchEnv :: String -> EnvTag -> Int -> SExpr -> EnvDecode [SExpr]
matchEnv context t arity e = case e of
  SList (SAtom k : fields)
    | parseEnvTag k == Just t ->
        if length fields == arity
          then eok fields
          else
            ewerr
              context
              ( "wrong number of fields for "
                  ++ envTagToString t
                  ++ ": expected "
                  ++ show arity
                  ++ ", got "
                  ++ show (length fields)
              )
  _ -> ewerr context ("expected (" ++ envTagToString t ++ " …), got " ++ show e)

-- | Match a variable-arity section and return its fields.
envSection :: String -> EnvTag -> SExpr -> EnvDecode [SExpr]
envSection context t e = case e of
  SList (SAtom k : fields) | parseEnvTag k == Just t -> eok fields
  _ -> ewerr context ("expected (" ++ envTagToString t ++ " …), got " ++ show e)

envAtomText :: String -> SExpr -> EnvDecode String
envAtomText _ (SAtom s) = eok s
envAtomText context e = ewerr context ("expected an atom, got " ++ show e)

-- | Encode the parity envelope.
--
-- The exact inverse of 'decodeMapCheckInput' for any value 'mapCheckInput'
-- produced; a hand-built value violating one of the invariants documented on
-- 'MapCheckInput' encodes fine and then fails to decode, exactly as
-- "Lara.Map.Wire"'s two codecs behave. Order-preserving throughout: members,
-- claims and alignments print in list order, so the frontend's ordering is
-- what reaches the file.
encodeMapCheckInput :: MapCheckInput -> SExpr
encodeMapCheckInput input =
  etagged
    ETMapCheckInput1
    [ etagged ETPolicy [SAtom (let PolicyId policy = mciPolicy input in policy)]
    , etagged
        ETBackends
        [ etagged ETBackend [SAtom backend, SAtom version]
        | (BackendId backend, version) <- mciBackends input
        ]
    , etagged ETMembers (map encodeMember (NE.toList (mciMembers input)))
    , etagged ETAlignments (map encodeAlignment (mciAlignments input))
    ]

encodeMember :: MapCheckMember -> SExpr
encodeMember member =
  etagged
    ETMember
    [ SAtom (aliasText (mcmAlias member))
    , SAtom (declaredPathText (mcmPath member))
    , etagged ETArtifact [SAtom (let Digest digest = mcmArtifact member in digest)]
    , etagged
        ETClaims
        [ etagged ETClaim [SAtom claim, encodeAtom proposition]
        | (PropId claim, proposition) <- mcmClaims member
        ]
    , encodeUnit (mcmUnit member)
    ]

-- | Decode a parity envelope from an already-parsed form, including every
-- self-consistency invariant a terminal input must satisfy (see the module
-- header).
decodeMapCheckInput :: SExpr -> Either MapWireError MapCheckInput
decodeMapCheckInput = runEnvDecode . decodeMapCheckInputM

-- | Decode a parity envelope from its text, mapping a located S-expression
-- parse failure into a located codec error. Exactly one top-level form is
-- accepted, mirroring 'Lara.Map.Wire.decodeMapManifestText'.
decodeMapCheckInputText :: String -> Either MapWireError MapCheckInput
decodeMapCheckInputText text = case parseSExpr text of
  Left (ParseError line column message) ->
    Left (MapWireError ("line " ++ show line ++ ", column " ++ show column) message)
  Right value -> decodeMapCheckInput value

decodeMapCheckInputM :: SExpr -> EnvDecode MapCheckInput
decodeMapCheckInputM value = do
  [policySection, backendsSection, membersSection, alignmentsSection] <-
    matchEnv context ETMapCheckInput1 4 value
  [policy] <- matchEnv "map check-input policy" ETPolicy 1 policySection
  policyIdValue <- PolicyId <$> envAtomText "map check-input policy" policy
  backends <- decodeBackends backendsSection
  members <- decodeMembers membersSection
  alignments <- do
    fields <- envSection "map check-input alignments" ETAlignments alignmentsSection
    mapM decodeAlignment fields
  -- The record is not assembled here. 'mkMapCheckInput' owns every invariant an
  -- envelope promises — including the shared-section agreement and alignment
  -- resolvability this door used to run inline — so a check added there is a
  -- check this door gains, and the two cannot report it differently.
  either efail eok
    (mkMapCheckInput policyIdValue backends members alignments)
  where
    context = "map check-input"

-- | The backend selection: duplicate-free and strictly ascending by
-- @(id, version)@, the same rule the manifest and the composite verdict carry,
-- so one selection has exactly one spelling in all three grammars.
decodeBackends :: SExpr -> EnvDecode [(BackendId, String)]
decodeBackends section = do
  fields <- envSection context ETBackends section
  backends <- mapM decodeBackend fields
  if strictlyAscending backends
    then eok backends
    else ewerr context "backends must be duplicate-free and ascending by (id, version)"
  where
    context = "map check-input backends"
    decodeBackend e = do
      [backend, version] <- matchEnv context ETBackend 2 e
      (,) . BackendId <$> envAtomText context backend <*> envAtomText context version

decodeMembers :: SExpr -> EnvDecode (NonEmpty MapCheckMember)
decodeMembers section = do
  fields <- envSection context ETMembers section
  members <- mapM decodeMember fields
  case NE.nonEmpty members of
    Nothing -> ewerr context "a map check-input declares at least one member"
    Just nonEmptyMembers -> case firstDuplicate (map mcmAlias members) of
      Just duplicate -> ewerr context ("duplicate member alias " ++ aliasText duplicate)
      Nothing -> eok nonEmptyMembers
  where
    context = "map check-input members"

decodeMember :: SExpr -> EnvDecode MapCheckMember
decodeMember e = do
  [alias, path, artifact, claimsSection, unitSection] <- matchEnv context ETMember 5 e
  aliasValue <- decodeAlias context alias
  pathValue <- do
    text <- envAtomText context path
    erequired context "path must be a nonempty atom" (mkDeclaredPath text)
  [digest] <- matchEnv context ETArtifact 1 artifact
  digestValue <- Digest <$> envAtomText context digest
  claims <- decodeClaims aliasValue claimsSection
  unit <- case decodeUnit unitSection of
    Left (WireError unitContext message) ->
      ewerr (context ++ " " ++ aliasText aliasValue ++ ": " ++ unitContext) message
    Right unit -> eok unit
  -- 'Lara.Wire.decodeUnit' scans a unit's argument ids and its groups for
  -- repeats and __not__ its leaves, and the Lean wire decoder does not either,
  -- so a repeated leaf id survives to here. It has to be refused, because
  -- 'Lara.Driver.buildGamma' is first-wins: one leaf would shadow the other,
  -- and every argument built on the shadowed one would be checked against a
  -- proposition its author never wrote — with no error anywhere. Decided per
  -- member, while there is still a member to name it against.
  case firstDuplicate [leaf | (LeafId leaf, _) <- unitLeaves unit] of
    Just duplicate ->
      ewerr
        (context ++ " " ++ aliasText aliasValue)
        ("duplicate leaf id " ++ duplicate)
    Nothing -> eok ()
  eok
    MapCheckMember
      { mcmAlias = aliasValue
      , mcmPath = pathValue
      , mcmArtifact = digestValue
      , mcmClaims = claims
      , mcmUnit = unit
      }
  where
    context = "map check-input member"

decodeAlias :: String -> SExpr -> EnvDecode MemberAlias
decodeAlias context e = do
  text <- envAtomText context e
  erequired
    context
    ("malformed member alias " ++ show text ++ ": expected nonempty [A-Za-z0-9_-]")
    (mkMemberAlias text)

-- | A member's claim names paired with their propositions, in declaration
-- order.
--
-- The names must be unique within the member, because @(alias, claim name)@ is
-- the map's reporting handle and a repeated name would give one status two
-- meanings — and because the resolution of an alignment coordinate is a
-- @lookup@, which is first-wins and would silently pick one of them.
decodeClaims :: MemberAlias -> SExpr -> EnvDecode [(PropId, Prop)]
decodeClaims alias section = do
  fields <- envSection context ETClaims section
  claims <- mapM decodeClaim fields
  case firstDuplicate (map fst claims) of
    Just (PropId duplicate) -> ewerr context ("duplicate claim name " ++ duplicate)
    Nothing -> eok claims
  where
    context = "map check-input claims of member " ++ aliasText alias
    decodeClaim e = do
      [claim, atom] <- matchEnv context ETClaim 2 e
      claimId <- PropId <$> envAtomText context claim
      proposition <- case decodeAtomSExpr atom of
        Left (WireError atomContext message) -> ewerr (context ++ ": " ++ atomContext) message
        Right p -> eok p
      eok (claimId, proposition)

-- | The alignment production, decoded by "Lara.Map.Wire"'s copy under this
-- door's own context prefix.
--
-- There is no second alignment grammar here. The envelope and the manifest
-- carry the same production, and 'Lara.Map.Wire.decodeAlignmentIn' is the one
-- place its twelve spellings are written down; @EnvTag@ keeps only the words
-- this grammar actually owns. See that function for why the @MapTag@\/@EnvTag@
-- split, which is right for the frozen core table, is wrong for a whole shared
-- production.
decodeAlignment :: SExpr -> EnvDecode Alignment
decodeAlignment = either efail eok . decodeAlignmentIn "map check-input"

-- | Every member's unit agrees with the first on the sections that come from
-- the __shared policy__ rather than from the member's own text.
--
-- On the @.laramap@ door this is a consequence, not a check: "Lara.Map.Load"
-- compares every member against the /manifest's/ policy, so any two members
-- that get this far agree with each other by transitivity, and
-- 'Lara.Map.Link.sharedSections' re-derives the same fact on the units it
-- merges. An envelope has no manifest policy file to compare against and no
-- loader behind it — its bytes are all a reader has — so the consequence has to
-- become the check. Refusing here is what stops a hand-written envelope from
-- linking two members that never ran under one policy, which is the one thing
-- the composite verdict would otherwise be silently wrong about.
sharedSectionsAgree :: NonEmpty MapCheckMember -> EnvDecode ()
sharedSectionsAgree (first :| rest) = List.foldl' step (eok ()) rest
  where
    unit0 = mcmUnit first
    step acc member = do
      _ <- acc
      case disagreement (mcmUnit member) of
        Just field ->
          ewerr
            context
            ( "members "
                ++ aliasText (mcmAlias first)
                ++ " and "
                ++ aliasText (mcmAlias member)
                ++ " disagree on the shared policy's "
                ++ field
            )
        Nothing -> eok ()

    disagreement unit
      | unitSigma unit /= unitSigma unit0 = Just "signature"
      | unitRules unit /= unitRules unit0 = Just "rules"
      | unitContraries unit /= unitContraries unit0 = Just "contraries"
      | unitExceptions unit /= unitExceptions unit0 = Just "exceptions"
      | unitTheories unit /= unitTheories unit0 = Just "theories"
      | unitGroupMode unit /= unitGroupMode unit0 = Just "duplicate-report mode"
      | otherwise = Nothing

    context = "map check-input members"

-- | Every alignment coordinate names a declared member, a claim that member
-- declares, and an argument position that claim has.
--
-- The same three conditions 'resolveRef' decides on the @.laramap@ door, made
-- a property of the envelope's own bytes: a driver reading this form has no
-- manifest to fall back on, so an unresolvable coordinate has to be refused
-- here rather than discovered halfway through evaluating an assertion.
resolvableAlignment :: NonEmpty MapCheckMember -> Alignment -> EnvDecode ()
resolvableAlignment members alignment = do
  _ <- resolvable (alignLeft alignment)
  _ <- resolvable (alignRight alignment)
  eok ()
  where
    context = "map check-input alignment"
    claims =
      Map.fromList [(mcmAlias member, mcmClaims member) | member <- NE.toList members]

    resolvable ref = case Map.lookup (refAlias ref) claims of
      Nothing ->
        ewerr context ("undeclared member alias " ++ aliasText (refAlias ref))
      Just memberClaims -> case lookup (refClaim ref) memberClaims of
        Nothing ->
          ewerr
            context
            ( "member "
                ++ aliasText (refAlias ref)
                ++ " declares no claim "
                ++ (let PropId claim = refClaim ref in claim)
            )
        Just (Prop _ arguments) -> case refCoord ref of
          CoordWhole -> eok ()
          CoordArg index
            | argIndexInt index < length arguments -> eok ()
            | otherwise ->
                ewerr
                  context
                  ( "claim "
                      ++ (let PropId claim = refClaim ref in claim)
                      ++ " of member "
                      ++ aliasText (refAlias ref)
                      ++ " has no argument "
                      ++ show (argIndexInt index)
                      ++ " (arity "
                      ++ show (length arguments)
                      ++ ")"
                  )
