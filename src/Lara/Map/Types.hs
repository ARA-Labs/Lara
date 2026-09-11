-- | The composition boundary of a multi-artifact /map/: the symbolic
-- vocabulary shared by every later stage of the map pipeline.
--
-- A map is a set of independently authored, independently checkable @.lara@
-- paper artifacts (its __members__), declared by a @.laramap@ manifest that
-- gives each member a local path and a unique __alias__. Nothing is hashed,
-- pinned, or cached: LARA rereads each member's current bytes, rechecks it
-- solo, qualifies its local identities by member alias, completes the
-- cross-member attacks, checks the one linked unit, and prints a composite
-- verdict. This module owns the types that boundary is stated in; the codecs
-- that turn them into bytes live in "Lara.Map.Wire", the loader in
-- @Lara.Map.Load@, the qualification and linking in @Lara.Map.Qualify@ /
-- @Lara.Map.Link@, and the CLI operation in @Lara.Map.Driver@.
--
-- == Why the identities are opaque
--
-- Two members may each declare a leaf called @e1@ and an argument called @a1@.
-- Linking them means the two must /not/ collide, and the map's own reports must
-- be able to say which member each identity came from. Both jobs are one
-- injective function, so 'QualifiedId' is opaque and built only by 'qualifyId':
-- an alias plus a local name, carried as a pair and observed in exactly two
-- ways — 'qualifiedKey', the length-framed identity form (injective, the only
-- thing a downstream identity may be derived from), and 'qualifiedDisplay',
-- the @alias::local@ form that is for human reports and is never an identity
-- and never a byte of a canonical verdict. Keeping the two apart in the type is
-- what stops a report string from silently becoming a key.
--
-- 'MemberAlias' is opaque for the same reason at one level down: an alias is
-- restricted to ASCII @[A-Za-z0-9_-]@, so it can never contain the @:@ that
-- frames a qualified key, and 'aliasText' is always a bare S-expression atom.
-- 'DeclaredPath' is opaque so that the path a verdict reports is provably the
-- one the manifest spelled, not a resolved absolute path the loader computed.
--
-- == Length framing
--
-- @qualifiedKey@ frames both halves with their UTF-8 byte length, the house
-- convention 'Lara.Strict.ND' uses for its source-atom keys:
--
-- @
-- frame s = show (utf8Length s) ++ ":" ++ s
-- qualifiedKey = concatMap frame [alias, local]     -- e.g. @7:paper_a2:e1@
-- @
--
-- The framing is reimplemented here rather than shared with
-- "Lara.Strict.ND": that module keeps @frame@ private because its frames are
-- part of a /frozen backend wire key/, and a map key is a different namespace
-- that must be free to move without perturbing a backend's bytes. The two
-- share a shape, deliberately not a function. 'parseQualifiedKey' is the
-- operational witness that the shape is injective, and
-- @lean\/Lara\/Map\/Qualify.lean@ carries the mechanized one: @qualifiedKey_inj@
-- recovers both halves of a key, and @qualifyLeaf_ne_of_alias_ne@ turns that
-- into the disjointness of two members' renamed leaf namespaces.
module Lara.Map.Types
  ( -- * Member aliases
    MemberAlias
  , mkMemberAlias
  , aliasText
    -- * Member-qualified local identities
  , QualifiedId
  , qualifyId
  , qualifiedKey
  , qualifiedDisplay
  , unqualifyId
  , parseQualifiedKey
    -- * Manifest-spelled paths
  , DeclaredPath
  , mkDeclaredPath
  , declaredPathText
    -- * Bounded indices
  , ArgIndex
  , mkArgIndex
  , argIndexInt
  , NodeIndex
  , mkNodeIndex
  , nodeIndexInt
    -- * Selectors, assertions, references
  , Coord (..)
  , sameSelectorKind
  , Assertion (..)
  , MapRef (..)
    -- * The manifest
  , MapMember (..)
  , Alignment (..)
  , MapQuestion (..)
  , MapManifest
  , mkMapManifest
  , mapPolicy
  , mapPolicyPath
  , mapBackends
  , mapMembers
  , mapAlignments
  , mapQuestions
    -- * The composite verdict
  , MapScope (..)
  , MapSchema (..)
  , MemberRecord (..)
  , MapNode (..)
  , MapStatus (..)
  , MapVerdict (..)
    -- * Diagnostics
  , MapWireError (..)
  , ContractField (..)
  , contractFieldText
  , MapBoundaryError (..)
  , MapRejectError (..)
  , MapError (..)
  , renderMapError
  , mapErrorExitCode
    -- * List predicates the map codecs share
  , firstDuplicate
  , strictlyAscending
  ) where

import Data.Char (isAlphaNum, isAscii, isDigit, ord)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import qualified Data.Set as Set

import Lara.AST
  ( ArgId
  , Binding
  , BackendId
  , Digest
  , Label
  , PolicyId (..)
  , PropId (..)
  , QuestionId
  , Rejection (..)
  , Status
  )
import Lara.Prop (Prop)
import Lara.Replay (CoreVersion)
import Lara.Wire
  ( Tag (TDupArgument, TDupRule, TIncompleteArgument, TMissingConflict)
  , rejectClassTag
  , tagToString
  )

-- ---------------------------------------------------------------------------
-- Member aliases
-- ---------------------------------------------------------------------------

-- | A member's unique short name inside one map, as declared by the manifest.
--
-- __Opaque.__ Build only with 'mkMemberAlias'; observe with 'aliasText'. The
-- restricted character set is load-bearing twice over: it keeps @:@ out of an
-- alias so 'qualifiedKey' stays unambiguous, and it keeps every alias inside
-- "Lara.Wire"'s bare-atom set so no manifest or verdict byte ever needs
-- quoting for an alias.
newtype MemberAlias = MemberAlias String
  deriving (Eq, Ord, Show)

-- | Build a member alias: a nonempty string of ASCII @[A-Za-z0-9_-]@ only.
--
-- 'Nothing' is a decode-boundary rejection, never a silent repair — an alias
-- the author cannot spell is an alias whose qualified keys they cannot predict.
mkMemberAlias :: String -> Maybe MemberAlias
mkMemberAlias name
  | not (null name)
  , all isAliasChar name =
      Just (MemberAlias name)
  | otherwise = Nothing

isAliasChar :: Char -> Bool
isAliasChar c = (isAscii c && isAlphaNum c) || c == '_' || c == '-'

-- | The alias text: always a bare S-expression atom.
aliasText :: MemberAlias -> String
aliasText (MemberAlias name) = name

-- ---------------------------------------------------------------------------
-- Member-qualified local identities
-- ---------------------------------------------------------------------------

-- | A local identity of one member, qualified by that member's alias.
--
-- __Opaque.__ Build only with 'qualifyId'. The value is carried as the
-- @(alias, local)@ pair rather than as its framed key so that 'unqualifyId'
-- and 'qualifiedDisplay' are total and cannot fail on a value that was already
-- built — a key stored as a string would have to be re-parsed to be read back,
-- turning two observers into two partial functions.
--
-- The local half is a bare 'String' because the same qualification applies to
-- three distinct source namespaces ('Lara.AST.LeafId', 'Lara.AST.ArgId',
-- 'Lara.AST.GroupId'); the qualifier is namespace-agnostic by design, and the
-- caller keeps the namespace in its own type on both sides of the call.
--
-- __Ordering.__ The derived 'Ord' is @(alias, local)@ lexicographic, /not/ the
-- order of 'qualifiedKey' (which sorts by frame length first). Deterministic
-- map output is ordered by this instance; the framed key is only an identity.
data QualifiedId = QualifiedId MemberAlias String
  deriving (Eq, Ord, Show)

-- | Qualify one member-local name by its member's alias.
qualifyId :: MemberAlias -> String -> QualifiedId
qualifyId = QualifiedId

-- | The injective identity form: both halves length-framed, so no pair of
-- distinct @(alias, local)@ inputs can produce one key. This is the only form
-- a downstream identity may be derived from.
qualifiedKey :: QualifiedId -> String
qualifiedKey (QualifiedId alias local) = renderFrames [aliasText alias, local]

-- | The human-readable form, @alias::local@.
--
-- __Reports only.__ It is not the sanctioned identity: nothing downstream may
-- derive a key from it, and no canonical verdict may contain a byte of it. Only
-- 'qualifiedKey' carries the length frames that make an identity safe to
-- concatenate, compare, or extend; a display string that happened to be unique
-- for today's inputs would be an identity by accident, which is exactly the
-- kind of invariant this module refuses to leave to chance.
qualifiedDisplay :: QualifiedId -> String
qualifiedDisplay (QualifiedId alias local) = aliasText alias ++ "::" ++ local

-- | Recover both halves of a qualified identity.
unqualifyId :: QualifiedId -> (MemberAlias, String)
unqualifyId (QualifiedId alias local) = (alias, local)

-- | Decode a framed 'qualifiedKey' back to the identity that produced it.
--
-- This is the operational injectivity witness: it is a left inverse of
-- 'qualifiedKey', it rejects non-canonical frame lengths (a leading @+@ or a
-- leading zero), a frame that does not end on a UTF-8 character boundary, and
-- any trailing bytes. The mechanized statement is @qualifiedKey_inj@ in
-- @lean\/Lara\/Map\/Qualify.lean@, proved through the same round-trip.
parseQualifiedKey :: String -> Maybe QualifiedId
parseQualifiedKey text = do
  (aliasPart, afterAlias) <- takeFrame text
  (localPart, rest) <- takeFrame afterAlias
  if null rest
    then flip QualifiedId localPart <$> mkMemberAlias aliasPart
    else Nothing

-- | UTF-8 byte length of a 'String' (the frame width).
utf8Length :: String -> Int
utf8Length = sum . map utf8Width

utf8Width :: Char -> Int
utf8Width c
  | ord c <= 0x7f = 1
  | ord c <= 0x7ff = 2
  | ord c <= 0xffff = 3
  | otherwise = 4

frame :: String -> String
frame s = show (utf8Length s) ++ ":" ++ s

renderFrames :: [String] -> String
renderFrames = concatMap frame

-- | Split one @LENGTH:PAYLOAD@ frame off the front, returning the payload and
-- the remainder.
takeFrame :: String -> Maybe (String, String)
takeFrame text = case span isDigit text of
  (digits, ':' : body) -> do
    width <- canonicalNat digits
    takeUtf8 width body
  _ -> Nothing

-- | A canonical decimal: nonempty digits, no leading zero unless the number
-- /is/ zero. Matching "Lara.Wire"'s @NAT@ rule keeps one spelling per number.
canonicalNat :: String -> Maybe Int
canonicalNat digits = case reads digits :: [(Int, String)] of
  [(n, "")] | n >= 0, show n == digits -> Just n
  _ -> Nothing

-- | Take exactly @n@ UTF-8 bytes' worth of characters, failing if the count
-- does not land on a character boundary or the input is too short.
takeUtf8 :: Int -> String -> Maybe (String, String)
takeUtf8 width
  | width < 0 = const Nothing
  | otherwise = go width []
  where
    go 0 acc rest = Just (reverse acc, rest)
    go remaining acc (c : cs) =
      let w = utf8Width c
       in if w <= remaining then go (remaining - w) (c : acc) cs else Nothing
    go _ _ [] = Nothing

-- ---------------------------------------------------------------------------
-- Manifest-spelled paths
-- ---------------------------------------------------------------------------

-- | A member or policy path exactly as the manifest spells it.
--
-- __Opaque, and deliberately not 'FilePath'.__ A map verdict must report the
-- /manifest-spelled/ path so that two people running the same manifest from
-- different directories get byte-identical verdicts. Making the declared path
-- its own type means the loader physically cannot put the absolute path it
-- resolved into the verdict: resolution produces a plain 'FilePath', which no
-- verdict field accepts.
newtype DeclaredPath = DeclaredPath String
  deriving (Eq, Ord, Show)

-- | Build a declared path: any nonempty atom. Nothing is resolved, normalised,
-- or checked for existence here — that is the loader's stage, against the
-- manifest's own directory.
mkDeclaredPath :: String -> Maybe DeclaredPath
mkDeclaredPath path
  | null path = Nothing
  | otherwise = Just (DeclaredPath path)

-- | The path text as declared.
declaredPathText :: DeclaredPath -> String
declaredPathText (DeclaredPath path) = path

-- ---------------------------------------------------------------------------
-- Bounded indices
-- ---------------------------------------------------------------------------

-- | An argument position inside one claim's proposition, as selected by an
-- alignment coordinate (the @n@ of @(arg n)@).
--
-- __Opaque__ so a negative index is unrepresentable: the encoder is total, and
-- a value that round-trips through the wire's canonical @NAT@ is guaranteed to
-- exist. Separate from 'NodeIndex' because the two name different things —
-- swapping them silently is exactly the confusion the newtypes prevent.
newtype ArgIndex = ArgIndex Int
  deriving (Eq, Ord, Show)

-- | Build a claim-coordinate argument position; must be non-negative.
mkArgIndex :: Int -> Maybe ArgIndex
mkArgIndex n
  | n >= 0 = Just (ArgIndex n)
  | otherwise = Nothing

-- | The argument position.
argIndexInt :: ArgIndex -> Int
argIndexInt (ArgIndex n) = n

-- | An argument index of the /linked/ unit — the compiled position a map node,
-- label, or edge endpoint refers to.
--
-- __Opaque__ for the same reason as 'ArgIndex': non-negative by construction.
newtype NodeIndex = NodeIndex Int
  deriving (Eq, Ord, Show)

-- | Build a linked-unit argument index; must be non-negative.
mkNodeIndex :: Int -> Maybe NodeIndex
mkNodeIndex n
  | n >= 0 = Just (NodeIndex n)
  | otherwise = Nothing

-- | The linked-unit argument index.
nodeIndexInt :: NodeIndex -> Int
nodeIndexInt (NodeIndex n) = n

-- ---------------------------------------------------------------------------
-- Selectors, assertions, references
-- ---------------------------------------------------------------------------

-- | What part of a claim an alignment coordinate points at: the whole
-- proposition, or one argument position of it.
--
-- A closed sum, so a coordinate vocabulary extension is a compile error at
-- every site rather than a string nobody matched.
data Coord
  = -- | the claim's proposition as a whole
    CoordWhole
  | -- | one argument position of the claim's proposition
    CoordArg ArgIndex
  deriving (Eq, Ord, Show)

-- | What an alignment asserts about the two coordinates it names: that they
-- denote the same thing, or that they deliberately differ.
--
-- An alignment is /checked/, never assumed: a false assertion is a map
-- rejection ('MRAlignmentFalse'), not a warning.
data Assertion = Same | Different
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | One coordinate of one member's claim: the member alias, the claim's local
-- name, and which part of it is meant.
data MapRef = MapRef
  { refAlias :: MemberAlias
  , refClaim :: PropId
  , refCoord :: Coord
  }
  deriving (Eq, Ord, Show)

-- ---------------------------------------------------------------------------
-- The manifest
-- ---------------------------------------------------------------------------

-- | One member of a map: its alias and the path the manifest spelled for it.
--
-- There is deliberately __no checksum, digest, or generated map id field__. A
-- map is rechecked from the members' current bytes on every run, so a pinned
-- hash would be a second source of truth that can only ever go stale; the
-- member's own declared @artifact@ identity, which the verdict carries
-- through, is the identity that already exists.
data MapMember = MapMember
  { memberAlias :: MemberAlias
  , memberPath :: DeclaredPath
  }
  deriving (Eq, Ord, Show)

-- | A declared cross-member alignment: two coordinates, what is asserted about
-- them, and who is accountable for the assertion.
--
-- The provenance triple is "Lara.AST"'s 'Binding' — the same
-- author\/rationale\/audit-status record the surface language already uses for
-- the untrusted link between a claim's prose and its formal target. An
-- alignment is the same kind of object one level up (an untrusted, attributed
-- link between two /formal/ coordinates), and reusing the record means the
-- audit vocabulary is spelled once.
data Alignment = Alignment
  { alignLeft :: MapRef
  , alignRight :: MapRef
  , alignAssertion :: Assertion
  , alignBinding :: Binding
  }
  deriving (Eq, Show)

-- | A map-level question: a natural-language question about two or more
-- member coordinates. Presentation only — it names what the map is /for/, and
-- carries no checker obligation.
data MapQuestion = MapQuestion
  { mapQuestionId :: QuestionId
  , mapQuestionRefs :: [MapRef]
  , mapQuestionNl :: String
  }
  deriving (Eq, Ord, Show)

-- | A decoded @.laramap@ manifest.
--
-- The manifest carries the policy and backend selection __explicitly__ so that
-- no member is privileged: shared-contract validation compares every member
-- against the manifest, not against whichever member happened to load first.
--
-- __The constructor is hidden.__ Every field below carries an invariant the
-- rest of the pipeline reads as a promise, and a manifest is decode-boundary
-- data: it arrives from a frontend the kernel does not control. Build one with
-- 'mkMapManifest', which returns the same 'MapWireError' the decoder would have
-- produced, or through 'Lara.Map.Wire.decodeMapManifest', which routes through
-- it.
--
-- __There is no @.Internal@ escape hatch, and none is needed.__ The field
-- selectors are exported, so a test that must build a manifest violating an
-- invariant on purpose does it by record-updating a valid one; what is gated is
-- /origination/. That is exactly the shape 'Lara.Replay.CheckInput' uses behind
-- @mkCheckInput@, which is this repo's own precedent for an input type and
-- likewise has no @.Internal@. Contrast 'Lara.Map.Load.CheckedMembers', which
-- exports no selectors and no smart constructor and therefore does have
-- "Lara.Map.Load.Internal".
--
-- Nonemptiness of 'mapMembers' is carried by 'NonEmpty' rather than by that
-- check, following 'Lara.Diagnostics.SeededSites': "declared, but nothing
-- declared" is the one state the boundary cannot report, so it is better as a
-- type error than as a diagnostic.
data MapManifest = MapManifest
  { mapPolicy :: PolicyId
  , mapPolicyPath :: DeclaredPath
  , -- | @(id, version)@ pairs, duplicate-free and ascending; shaped exactly
    -- like 'Lara.Replay.replayBackends' so the contract check is @==@.
    mapBackends :: [(BackendId, String)]
  , -- | Aliases unique, in manifest order. Nonemptiness is the type's.
    mapMembers :: NonEmpty MapMember
  , -- | Each alignment's two coordinates select the same kind of target: a
    -- pair mixing 'CoordWhole' with @'CoordArg' n@ does not encode-decode.
    mapAlignments :: [Alignment]
  , -- | Each question relates at least two references.
    mapQuestions :: [MapQuestion]
  }
  deriving (Eq, Show)

-- | Build a manifest, or say which documented invariant the fields break.
--
-- The sanctioned constructor. Each check reproduces the decoder's own context
-- and message verbatim, so a manifest built here and one decoded from bytes
-- fail identically; 'Lara.Map.Wire.decodeMapManifest' calls this rather than
-- assembling the record itself, which is what keeps the two in step.
--
-- Order of checks follows the manifest's own section order — backends, members,
-- alignments, questions — so a value breaking two invariants names the earlier
-- section, matching the decoder, which stops at the first section that fails.
mkMapManifest
  :: PolicyId
  -> DeclaredPath
  -> [(BackendId, String)]
  -> NonEmpty MapMember
  -> [Alignment]
  -> [MapQuestion]
  -> Either MapWireError MapManifest
mkMapManifest policy policyPath backends members alignments questions
  | not (strictlyAscending backends) =
      Left
        ( MapWireError
            "map backends"
            "backends must be duplicate-free and ascending by (id, version)"
        )
  | Just duplicate <- firstDuplicate (map memberAlias (NE.toList members)) =
      Left (MapWireError "map members" ("duplicate member alias " ++ aliasText duplicate))
  | any mixedSelector alignments =
      Left
        ( MapWireError
            "map alignment"
            "an alignment's two coordinates must both be whole or both be (arg n)"
        )
  | any ((< 2) . length . mapQuestionRefs) questions =
      Left (MapWireError "map question" "a map question relates at least two references")
  | otherwise =
      Right
        MapManifest
          { mapPolicy = policy
          , mapPolicyPath = policyPath
          , mapBackends = backends
          , mapMembers = members
          , mapAlignments = alignments
          , mapQuestions = questions
          }
  where
    mixedSelector alignment =
      not (sameSelectorKind (refCoord (alignLeft alignment)) (refCoord (alignRight alignment)))

-- | Whether two coordinates select the same kind of target.
--
-- A fact about the frozen 'Coord' type, so it lives beside it, and it is the
-- only copy: the manifest codec, the envelope codec and the smart constructors
-- all read this one (issue #317).
sameSelectorKind :: Coord -> Coord -> Bool
sameSelectorKind CoordWhole CoordWhole = True
sameSelectorKind (CoordArg _) (CoordArg _) = True
sameSelectorKind _ _ = False

-- ---------------------------------------------------------------------------
-- List predicates the map codecs share
-- ---------------------------------------------------------------------------

-- | The first element that occurs twice, in first-repeat order: the earliest
-- position at which an element equal to an earlier one appears decides the
-- answer, so @[a, b, b, a]@ reports @b@, and a three-way repeat reports its
-- element once.
--
-- The single copy for the whole map pipeline — "Lara.Map.Wire",
-- "Lara.Map.Driver", "Lara.Map.Load" and 'mkMapManifest' all call it. They used
-- to carry one each, which nothing asserted agreed (issue #317); a decoder that
-- accepts what its sibling refuses is the failure that would have surfaced.
-- Not to be confused with @Lara.Check.firstDuplicate@, which scans a unit's
-- /support terms/ and reports index pairs.
firstDuplicate :: Ord a => [a] -> Maybe a
firstDuplicate = go Set.empty
  where
    go _ [] = Nothing
    go seen (x : xs)
      | x `Set.member` seen = Just x
      | otherwise = go (Set.insert x seen) xs

-- | Whether a list is strictly ascending — equivalently, duplicate-free and
-- sorted — so that a section it guards has exactly one spelling.
strictlyAscending :: Ord a => [a] -> Bool
strictlyAscending xs = and (zipWith (<) xs (drop 1 xs))

-- ---------------------------------------------------------------------------
-- The composite verdict
-- ---------------------------------------------------------------------------

-- | The scope marker a composite verdict opens with.
--
-- A one-constructor sum on purpose (mirroring 'Lara.Replay.CoreVersion'): the
-- marker exists so no consumer can mistake these bytes for a solo
-- 'Lara.Wire.Verdict', and making it a decoded field rather than an unread
-- literal means a future second scope is an additive constructor.
data MapScope = ScopeMap
  deriving (Eq, Show, Enum, Bounded)

-- | The composite verdict's schema identity, carried inside the verdict so a
-- consumer that has never heard of this schema fails to decode rather than
-- half-reading it.
data MapSchema = MapVerdictSchemaV1
  deriving (Eq, Show, Enum, Bounded)

-- | A member as a verdict reports it: its alias, its manifest-spelled path,
-- and the @artifact@ identity the member itself declared, carried through
-- unchanged. The map computes no digest of its own.
data MemberRecord = MemberRecord
  { mrAlias :: MemberAlias
  , mrPath :: DeclaredPath
  , mrArtifact :: Digest
  }
  deriving (Eq, Ord, Show)

-- | One member-local argument handle and the linked-unit index it resolved to.
--
-- Structurally identical support terms from different members merge into one
-- linked argument, so several nodes may share an index; every original
-- @(alias, local ArgId)@ handle is retained so a report can always name where
-- an argument came from.
data MapNode = MapNode
  { mnAlias :: MemberAlias
  , mnArg :: ArgId
  , mnIndex :: NodeIndex
  }
  deriving (Eq, Ord, Show)

-- | One map-relative claim status: which member's claim, the proposition
-- queried, and its four-state status in the linked unit.
--
-- The status is the ordinary four-state 'Status', with no
-- @evidence-blocked@ counterpart: a member whose admission or group-pruning
-- audit is nonempty is refused at load, so in a map no query can be blocked.
data MapStatus = MapStatus
  { msAlias :: MemberAlias
  , msClaim :: PropId
  , msAtom :: Prop
  , msStatus :: Status
  }
  deriving (Eq, Show)

-- | The composite verdict: the map's identity, its members, and the linked
-- unit's grounded result reported per member.
data MapVerdict = MapVerdict
  { mvScope :: MapScope
  , mvSchema :: MapSchema
  , mvCore :: CoreVersion
  , mvPolicy :: PolicyId
  , -- | @(id, version)@ pairs, duplicate-free and ascending — the same
    -- invariant 'mapBackends' carries, because 'decodeBackends' enforces
    -- ascent on both grammars.
    mvBackends :: [(BackendId, String)]
  , -- | Aliases unique, in manifest order. Nonemptiness is the type's, for the
    -- reason 'mapMembers' gives: a composite verdict over no members would
    -- accept vacuously over an empty universe, and the boundary cannot tell
    -- that apart from a verdict whose members were dropped.
    mvMembers :: NonEmpty MemberRecord
  , -- | Member order, then that member's own declaration order. Each
    -- @('mnAlias', 'mnArg')@ handle occurs once, each 'mnAlias' is declared in
    -- 'mvMembers', and the 'mnIndex' values cover __exactly__ the labelled
    -- arguments — every one of them is @< length 'mvLabels'@, and every
    -- labelled index has at least one handle. A linked argument exists because
    -- some member declared its support term, so an argument with no handle
    -- would be one that arose from nobody.
    mvNodes :: [MapNode]
  , -- | Ascending index, covering exactly @0 .. n-1@. This section pins @n@ for
    -- the two that follow.
    mvLabels :: [(NodeIndex, Label)]
  , -- | Strictly ascending lexicographic @(source, target)@ — which also makes
    -- it duplicate-free — with both endpoints @< length 'mvLabels'@.
    mvEdges :: [(NodeIndex, NodeIndex)]
  , -- | Member order, then that member's own claim declaration order. Each
    -- 'msAlias' is declared in 'mvMembers', and each @('msAlias', 'msClaim')@
    -- handle occurs __once__ — that pair is what a reader resolves a status by,
    -- so a repeat would make @lookup@ silently first-wins over two rows that may
    -- disagree. 'MBDuplicateClaim' holds a member to the same rule.
    mvStatuses :: [MapStatus]
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Diagnostics
-- ---------------------------------------------------------------------------

-- | A map codec failure: the offending grammar position and the reason.
--
-- Deliberately a separate type from 'Lara.Wire.WireError', and defined here
-- rather than in "Lara.Map.Wire", for two reasons: the map grammar is not the
-- frozen @lara-core\@0.2@ grammar and must be free to move without touching
-- it, and 'MapBoundaryError' has to name it, which a codec-side definition
-- would turn into an import cycle. "Lara.Map.Wire" re-exports it so a codec
-- consumer still needs one import.
data MapWireError = MapWireError
  { mweContext :: String
  , mweMessage :: String
  }
  deriving (Eq, Show)

-- | Which part of the shared contract a member disagreed with the manifest
-- about. Structures are compared, never names, so formatting-only differences
-- pass and a redefinition under a shared name fails.
data ContractField
  = -- | the member's declared policy id is not the manifest's
    CFPolicyId
  | -- | the parsed 'Lara.AST.Policy' values differ
    CFPolicyStructure
  | -- | the elaborated units' signatures differ
    CFSignature
  | -- | the units' theory sets differ, by label or by payload
    CFTheories
  | -- | the member's selected backends are not the manifest's
    CFBackends
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The single spelling table for contract-field names in diagnostics.
contractFieldText :: ContractField -> String
contractFieldText field = case field of
  CFPolicyId -> "policy id"
  CFPolicyStructure -> "policy structure"
  CFSignature -> "signature"
  CFTheories -> "theories"
  CFBackends -> "backend selection"

-- | Everything that makes a map ill-formed rather than unsupported: the map
-- could not be read, decoded, or resolved at all. Every constructor exits 2.
data MapBoundaryError
  = -- | manifest or verdict bytes failed to decode
    MBWire MapWireError
  | -- | a resolved path could not be read (the resolved path, then the reason)
    MBUnreadable FilePath String
  | -- | two aliases resolve to one file (both aliases, then the resolved file
    -- they share). Only the loader can catch this: the codec deliberately never
    -- resolves a path, so two spellings of one file are indistinguishable to
    -- it. Member-list emptiness and alias /uniqueness/, by contrast, are
    -- settled by the codec and reach here as 'MBWire' — they have no
    -- constructor of their own.
    --
    -- __The third field is a resolved 'FilePath', not a 'DeclaredPath', and
    -- that is a correction rather than an oversight.__ When the field was a
    -- declared path it implicitly assumed the two aliases had /spelled/ the
    -- same thing; a symlink, or a relative path beside an absolute one, breaks
    -- that assumption and there is then no single manifest spelling to report.
    -- What the two members genuinely share is the canonical file the loader
    -- resolved them to, and only a 'FilePath' can name it — the same resolved
    -- path 'MBUnreadable' already carries, for the same reason. Nothing is
    -- weakened by the change: a 'DeclaredPath' guards the /verdict's/ bytes,
    -- and no verdict field accepts a 'MapBoundaryError'.
    MBDuplicatePath MemberAlias MemberAlias FilePath
  | -- | the manifest names one policy id and the policy file it points at
    -- declares another (the manifest's id, then the file's). The bytes decoded
    -- perfectly, so this is deliberately __not__ an 'MBWire': the manifest is
    -- internally inconsistent, not malformed.
    --
    -- It exits 2 with the rest of this sum because the map cannot even be said
    -- to be /about/ a policy: the shared contract every member is compared
    -- against is exactly the pair this constructor reports as contradictory, so
    -- the manifest is unusable rather than merely rejected. Reporting it here,
    -- once, is also what stops it from surfacing as an 'MRContract' against
    -- every member in turn for a disagreement none of them caused.
    MBManifestPolicyMismatch PolicyId PolicyId
  | -- | the policy file the manifest points at could not be understood;
    -- carries that file's own boundary text.
    --
    -- Parallel to 'MBMemberSource', but for the manifest's own policy file,
    -- which has no member to attribute it to. Deliberately __not__ an
    -- 'MBWire': the manifest's bytes decoded perfectly and a /different/ file
    -- failed to parse, so dressing it as a codec error would name the wrong
    -- file and the wrong kind of failure. The unreadable case is not here — a
    -- path the loader resolved and could not open is 'MBUnreadable', which
    -- names that resolved path.
    MBManifestPolicySource String
  | -- | a member's own source boundary rejected it; carries its exit-2 text
    MBMemberSource MemberAlias String
  | -- | a reference names an alias no member declares
    MBUnknownAlias MemberAlias
  | -- | a member declares one claim name twice (the member, then the repeated
    -- name)
    --
    -- __The map owns this rule, and the @.lara@ frontend does not.__
    -- 'Lara.Elaborate.prepareSource' refuses a repeated @leaf@, @arg@ or group
    -- id but says nothing about a repeated @claim@ id, so a member declaring
    -- one twice checks perfectly well on its own — its two @status@ rows are
    -- simply the same query asked twice, which a solo verdict reports by
    -- proposition and not by name.
    --
    -- A map cannot be so relaxed, because @(member alias, claim name)@ is the
    -- handle its @statuses@ section is keyed by. Two rows under one handle
    -- would give one handle two meanings, and every consumer resolving a
    -- coordinate would have to pick one — which is exactly what an alignment
    -- coordinate does, by a first-wins @lookup@. It is a __boundary__ failure
    -- rather than a rejection because nothing has been decided about the map:
    -- the member cannot be /reported on/ in a map's vocabulary at all.
    MBDuplicateClaim MemberAlias PropId
  | -- | a reference names a claim the member does not declare
    MBUnknownClaim MemberAlias PropId
  | -- | @(arg n)@ past the claim's arity (member, claim, requested, arity)
    MBCoordinateOutOfRange MemberAlias PropId ArgIndex Int
  | -- | two coordinates in one alignment or question mix 'CoordWhole' with
    -- @'CoordArg' n@ (the two references' members)
    MBMixedSelector MemberAlias MemberAlias
  deriving (Eq, Show)

-- | Everything a well-formed map can be rejected /for/. Every constructor
-- exits 1: the map was understood, and the answer is no.
data MapRejectError
  = -- | a member disagrees with the manifest's shared contract
    MRContract MemberAlias ContractField
  | -- | a member carries a nonempty admission or group-pruning audit, which a
    -- map does not support; carries the audit summary.
    --
    -- The member is otherwise fine: it checks on its own, and it agrees with
    -- the manifest. What stopped it is that v1 __chose not to support__
    -- quarantined or pruned material, so the operator's remedy is that this
    -- feature does not cover their artifact yet. That is a different situation
    -- from 'MRMemberAdmissionStop', which is the two being deliberately kept
    -- apart.
    MRUnsupportedAdmission MemberAlias String
  | -- | the shared policy's admission table classed one of the member's leaves
    -- @reject@, stopping the source before it produced a unit; carries the
    -- member's own rendered admission rejection.
    --
    -- Deliberately __not__ 'MRMemberRejected': that constructor carries a
    -- 'Rejection', and a §4.3 admission stop has no rejection class — there is
    -- no @R8@ in 'Lara.AST.RejectClass', which is why the solo @.lara@ door
    -- prints 'Lara.Admission.renderAdmissionRejection' instead of a verdict for
    -- it. Filling the field with an invented class would put a fiction in a
    -- diagnostic.
    --
    -- Deliberately __not__ 'MRUnsupportedAdmission' either, though both are
    -- admission-caused and both exit 1. That one means the map declined to
    -- handle a member; this one means the member genuinely fails the policy the
    -- map is checking under, and the remedy is to fix the artifact or the
    -- policy. Folding them together would give an operator one line for two
    -- different jobs.
    MRMemberAdmissionStop MemberAlias String
  | -- | a member does not check on its own
    MRMemberRejected MemberAlias Rejection
  | -- | a declared alignment does not hold (its manifest position, 0-based,
    -- and what it asserted)
    MRAlignmentFalse Int Assertion
  | -- | the linked unit does not check
    MRLinkRejected Rejection
  | -- | the linked unit could not be built (a structural boundary with no
    -- rejection class of its own)
    MRLinkBoundary String
  deriving (Eq, Show)

-- | A map failure: ill-formed input, or a checked map whose answer is no.
data MapError
  = MapBoundary MapBoundaryError
  | MapReject MapRejectError
  deriving (Eq, Show)

-- | The one place the exit-code split lives: an ill-formed map exits 2, a
-- rejected map exits 1. Success exits 0 with the composite verdict on stdout.
mapErrorExitCode :: MapError -> Int
mapErrorExitCode err = case err of
  MapBoundary _ -> 2
  MapReject _ -> 1

-- | One @stderr@ line, naming the member and the stage whenever the error has
-- them. Never multi-line: the driver prints exactly this and nothing else, so
-- a caller can attribute a failure without parsing a verdict that was never
-- printed.
--
-- Several payloads are free strings from outside this module — a codec
-- context and message, a filesystem error, a member's own exit-2 text, an
-- admission-audit summary, a link-boundary reason — and any of them may
-- contain a newline. 'oneLine' folds those to spaces at every point of use, so
-- the single-line promise is a property of this function rather than an
-- assumption about its callers.
--
-- __A 'PolicyId' and a 'PropId' are free strings too__, and that is less
-- obvious than it looks: both reach a diagnostic from a wire atom, and
-- "Lara.Map.Wire" reads an atom through 'Lara.Wire.parseSExpr', which accepts a
-- __quoted__ atom with a @\\n@ escape in it. A manifest spelling
-- @(policy "a\\nb" p.lara)@ or @(ref paper_a "c\\n1" whole)@ therefore
-- carries a newline into an id, and every id is spelled through 'policyIdText'
-- or 'propIdText' for exactly that reason. 'aliasText' needs no such treatment:
-- 'mkMemberAlias' restricts an alias to ASCII @[A-Za-z0-9_-]@.
--
-- Rejection classes are spelled through "Lara.Wire"'s frozen tag table, so a
-- map diagnostic and a solo verdict name a rejection identically. Assertions
-- are deliberately /not/: they are rendered as prose ("identical"\/"distinct")
-- rather than as their wire tokens, so no diagnostic line can be mistaken for
-- canonical bytes.
renderMapError :: MapError -> String
renderMapError err = case err of
  MapBoundary boundary -> renderBoundaryError boundary
  MapReject reject -> renderRejectError reject

renderBoundaryError :: MapBoundaryError -> String
renderBoundaryError err = case err of
  MBWire (MapWireError context message) ->
    "map codec: " ++ oneLine context ++ ": " ++ oneLine message
  MBUnreadable path reason ->
    "map source: cannot read " ++ oneLine path ++ ": " ++ oneLine reason
  MBDuplicatePath first second path ->
    "map manifest: members "
      ++ aliasText first
      ++ " and "
      ++ aliasText second
      ++ " resolve to the same file "
      ++ oneLine path
  MBManifestPolicySource message ->
    "map manifest policy: " ++ oneLine message
  MBManifestPolicyMismatch declared actual ->
    "map manifest: declares policy "
      ++ policyIdText declared
      ++ ", but its policy file declares "
      ++ policyIdText actual
  MBMemberSource alias message ->
    "map member " ++ aliasText alias ++ ": " ++ oneLine message
  MBUnknownAlias alias ->
    "map manifest: reference to undeclared member alias " ++ aliasText alias
  MBDuplicateClaim alias claim ->
    "map member "
      ++ aliasText alias
      ++ ": declares claim "
      ++ propIdText claim
      ++ " more than once, so a map status would have two rows under one handle"
  MBUnknownClaim alias claim ->
    "map member " ++ aliasText alias ++ ": undeclared claim " ++ propIdText claim
  MBCoordinateOutOfRange alias claim index arity ->
    "map member "
      ++ aliasText alias
      ++ ": claim "
      ++ propIdText claim
      ++ " has no argument "
      ++ show (argIndexInt index)
      ++ " (arity "
      ++ show arity
      ++ ")"
  MBMixedSelector first second ->
    "map manifest: coordinates of members "
      ++ aliasText first
      ++ " and "
      ++ aliasText second
      ++ " mix a whole-claim selector with an argument selector"

renderRejectError :: MapRejectError -> String
renderRejectError err = case err of
  MRContract alias field ->
    "map contract: member "
      ++ aliasText alias
      ++ " disagrees with the manifest on "
      ++ contractFieldText field
  MRUnsupportedAdmission alias summary ->
    "map member "
      ++ aliasText alias
      ++ ": a nonempty admission or group-pruning audit is unsupported in a map: "
      ++ oneLine summary
  MRMemberAdmissionStop alias reason ->
    "map member "
      ++ aliasText alias
      ++ ": the policy's admission table rejected a leaf: "
      ++ oneLine reason
  MRMemberRejected alias rejection ->
    "map member " ++ aliasText alias ++ " rejected: " ++ rejectionText rejection
  MRAlignmentFalse position assertion ->
    "map alignment "
      ++ show position
      ++ ": the two coordinates are asserted to be "
      ++ assertionProse assertion
      ++ ", and they are not"
  MRLinkRejected rejection ->
    "map link rejected: " ++ rejectionText rejection
  MRLinkBoundary message ->
    "map link boundary: " ++ oneLine message

-- | The one place a claim name is spelled in a diagnostic. Folded, because a
-- 'PropId' can carry a newline in from a quoted wire atom — see
-- 'renderMapError'.
propIdText :: PropId -> String
propIdText (PropId claim) = oneLine claim

-- | A rejection class, spelled through "Lara.Wire"'s frozen table.
rejectionText :: Rejection -> String
rejectionText rejection =
  tagToString $ case rejection of
    DuplicateRule -> TDupRule
    DuplicateArgument -> TDupArgument
    IncompleteArgument -> TIncompleteArgument
    MissingConflict -> TMissingConflict
    RejectClass rejectClass -> rejectClassTag rejectClass

-- | Fold every newline (and carriage return) in a free-text payload to a
-- space, so one error is one line no matter what a filesystem, a member's
-- source boundary, or an audit summary put in it.
oneLine :: String -> String
oneLine = map (\c -> if c == '\n' || c == '\r' then ' ' else c)

-- | The one place a policy id is spelled in a diagnostic. Folded, for the
-- reason 'propIdText' is.
policyIdText :: PolicyId -> String
policyIdText (PolicyId pid) = oneLine pid

-- | Prose for an assertion in a diagnostic — deliberately not its wire token.
assertionProse :: Assertion -> String
assertionProse assertion = case assertion of
  Same -> "identical"
  Different -> "distinct"
