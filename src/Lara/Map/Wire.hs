{-# LANGUAGE DerivingVia #-}

-- | The S-expression codecs of the multi-artifact map: the @lara-map\@1@
-- manifest (input) and the @map-verdict\@1@ composite verdict (output).
--
-- This is the map's decode boundary. Raw 'String's exist here and nowhere
-- deeper: every atom this module reads is parsed into the symbolic vocabulary
-- of "Lara.Map.Types" — opaque aliases, opaque declared paths, opaque indices,
-- closed selector\/assertion sums — before any later stage sees it, and every
-- atom it writes is rendered from that vocabulary through exactly one table.
--
-- == Why a second tag vocabulary
--
-- 'MapTag' is a /separate/ closed sum from 'Lara.Wire.Tag', with its own single
-- 'mapTagToString' table, even though the two overlap on spellings like
-- @policy@, @backend@, and @status@. The overlap is deliberate — the map
-- grammar names the same concepts with the same words, so a reader sees one
-- vocabulary — but the tables must stay independent: @lara-core\@0.2@'s tag
-- table is frozen and byte-pinned by conformance goldens and the Lean driver's
-- mirrored table, so the map grammar must be unable to perturb it. Growing
-- 'Lara.Wire.Tag' for a map keyword would put a non-core spelling inside the
-- frozen vocabulary and force the Lean mirror to grow with it.
--
-- The one thing the two grammars share is the @\<atom\>@ production: a map
-- verdict's statuses carry propositions in exactly 'Lara.Wire.encodeAtom'\'s
-- form, read back by 'Lara.Wire.decodeAtomSExpr'. Propositions are core
-- objects, and a map that spelled them differently would be a second
-- proposition syntax to keep in step. The @lara-core\@0.2@ marker likewise
-- comes from 'Lara.Wire.coreVersionText'.
--
-- == Manifest grammar
--
-- Exactly one top-level form; all five sections required, in this order; no
-- unknown tag anywhere.
--
-- @
-- \<manifest\>   ::= (lara-map\@1 (policy POLICY-ID PATH)
--                              (backends (backend BACKEND-ID VERSION)*)
--                              (members (member ALIAS PATH)+)
--                              (alignments ALIGNMENT*)
--                              (questions MAPQUESTION*))
-- ALIGNMENT   ::= (alignment REF REF ASSERTION (author NAME)
--                            (audit-status AUDIT) (rationale TEXT))
-- MAPQUESTION ::= (question QUESTION-ID (refs REF REF+) (nl TEXT))
-- REF         ::= (ref ALIAS CLAIM-NAME COORD)
-- COORD       ::= whole | (arg NAT)
-- ASSERTION   ::= same | different
-- AUDIT       ::= unreviewed | reviewed | disputed
-- @
--
-- A member entry carries __only__ an alias and a path: there is no checksum
-- field and no generated map id. A map is rechecked from the members' current
-- bytes on every run, so a pinned hash would be a second source of truth whose
-- only possible future is to go stale.
--
-- == Composite verdict grammar
--
-- @
-- \<map-verdict\> ::= (map-verdict\@1 (scope map) (schema lara-map-verdict\@1)
--                                  (core lara-core\@0.2) (policy POLICY-ID)
--                                  (backends (backend BACKEND-ID VERSION)*)
--                                  (members (member ALIAS PATH (artifact DIGEST))+)
--                                  (nodes (node ALIAS ARG-ID INDEX)*)
--                                  (labels (INDEX LABEL)*)
--                                  (edges (SRC TGT)*)
--                                  (statuses (status ALIAS CLAIM-NAME \<atom\> STATUS)*))
-- LABEL  ::= in | out | undec
-- STATUS ::= gap | justified | contested | defeated
-- @
--
-- @(scope map)@ leads so that no consumer can confuse these bytes with a solo
-- @(verdict …)@. @PATH@ is the manifest-spelled path, never a resolved one
-- (that is what 'DeclaredPath' enforces), and @DIGEST@ is the member's own
-- declared @artifact@ identity carried through unchanged. There is no
-- @evidence-blocked@ status: a member with a nonempty admission or
-- group-pruning audit is refused at load, so in a map no query can be blocked.
--
-- == What the codec checks, and what it leaves to the loader
--
-- The rule is: __the codec enforces what one form's own bytes determine; the
-- loader enforces what needs the members loaded.__ So the manifest decoder
-- rejects an empty @members@ section, a duplicate or ill-spelled alias, an
-- empty path, a non-canonical @NAT@, a @backends@ list that is not strictly
-- ascending by @(id, version)@, a question with fewer than two references, and
-- an alignment that mixes @whole@ with @(arg n)@ — all of them properties of
-- the manifest text alone. It does /not/ resolve a path, look a claim up, or
-- check that a reference names a declared alias: those get member-attributed
-- diagnostics ('MBUnknownAlias', 'MBUnknownClaim',
-- 'MBCoordinateOutOfRange', 'MBMixedSelector' for a question's reference list)
-- from the stage that has the members in hand. Every one of these, codec or
-- loader, is a 'MapBoundary' error and exits 2, so the split is a matter of
-- which diagnostic the operator reads, never of which inputs are accepted.
--
-- A composite verdict is terminal — no later stage will ever revisit it — so
-- its decoder additionally checks self-consistency: aliases in @nodes@ and
-- @statuses@ are declared in @members@, each @(alias, ARG-ID)@ handle occurs
-- once, @labels@ covers exactly @0 .. n-1@ ascending, @edges@ are strictly
-- ascending lexicographic, and every index is in range. This mirrors the two
-- extra invariants "Lara.Wire" checks at its own decode boundary (unique
-- argument ids, declared attack endpoints): wire well-formedness, not a
-- checker rejection.
--
-- For any value satisfying the invariants documented on 'MapManifest' and
-- 'MapVerdict', encoding is the exact inverse of decoding. That proviso is not
-- decoration: those record constructors are exported, so a caller can build a
-- manifest with no members or a verdict whose labels skip an index, and this
-- decoder will rightly refuse the bytes its own encoder produced. The types
-- carry the invariants in Haddock, not in the constructors, and the test
-- generators are written to respect them.
--
-- Encoding is unconditionally canonical: equal values print equal bytes, and
-- the encoder preserves list order rather than sorting, so the ordering the
-- driver computed is the ordering that reaches the file.
module Lara.Map.Wire
  ( -- * The closed map tag vocabulary
    MapTag (..)
  , mapTagToString
  , parseMapTag
    -- * Manifest codec
  , MapWireError (..)
  , encodeMapManifest
  , decodeMapManifest
    -- * The alignment production, shared with the parity envelope
  , encodeAlignment
  , decodeAlignmentIn
  , decodeMapManifestText
    -- * Composite verdict codec
  , encodeMapVerdict
  , decodeMapVerdict
  ) where

import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Lara.AST
  ( ArgId (..)
  , AuditStatus (..)
  , BackendId (..)
  , Binding (..)
  , Digest (..)
  , Label (..)
  , PolicyId (..)
  , PropId (..)
  , QuestionId (..)
  , Status (..)
  )
import Lara.Map.Types
import Lara.Prop (Prop)
import Lara.Replay (CoreVersion (..))
import Lara.Strict (SExpr (..))
import Lara.Wire
  ( ParseError (..)
  , WireError (..)
  , coreVersionText
  , decodeAtomSExpr
  , encodeAtom
  , parseSExpr
  )

-- ---------------------------------------------------------------------------
-- The closed map tag vocabulary
-- ---------------------------------------------------------------------------

-- | Every keyword of the map grammars, as a closed sum type. The concrete
-- spellings live in exactly one place ('mapTagToString'); @mapTagTable@ derives
-- the reverse lookup from that function by enumerating the type.
--
-- Deliberately disjoint from 'Lara.Wire.Tag' as a /type/ while overlapping it
-- on several spellings; see the module header for why the tables must not be
-- merged.
data MapTag
  = -- manifest envelope
    MTLaraMap1
  | MTPolicy | MTBackends | MTBackend | MTMembers | MTMember
  | MTAlignments | MTAlignment | MTQuestions | MTQuestion
  | MTRefs | MTRef | MTNl
    -- selectors and assertions
  | MTWhole | MTArg | MTSame | MTDifferent
    -- alignment provenance (the surface binding block's vocabulary)
  | MTAuthor | MTRationale | MTAuditStatus
  | MTUnreviewed | MTReviewed | MTDisputed
    -- composite verdict envelope
  | MTMapVerdict1 | MTScope | MTMap | MTSchema | MTMapVerdictSchema1 | MTCore
  | MTArtifact | MTNodes | MTNode | MTLabels | MTEdges | MTStatuses | MTStatus
    -- grounded labels and four-state statuses
  | MTIn | MTOut | MTUndec
  | MTGap | MTJustified | MTContested | MTDefeated
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The on-the-wire spelling of a map keyword.
mapTagToString :: MapTag -> String
mapTagToString t = case t of
  MTLaraMap1 -> "lara-map@1"
  MTPolicy -> "policy"; MTBackends -> "backends"; MTBackend -> "backend"
  MTMembers -> "members"; MTMember -> "member"
  MTAlignments -> "alignments"; MTAlignment -> "alignment"
  MTQuestions -> "questions"; MTQuestion -> "question"
  MTRefs -> "refs"; MTRef -> "ref"; MTNl -> "nl"
  MTWhole -> "whole"; MTArg -> "arg"
  MTSame -> "same"; MTDifferent -> "different"
  MTAuthor -> "author"; MTRationale -> "rationale"
  MTAuditStatus -> "audit-status"
  MTUnreviewed -> "unreviewed"; MTReviewed -> "reviewed"
  MTDisputed -> "disputed"
  MTMapVerdict1 -> "map-verdict@1"
  MTScope -> "scope"; MTMap -> "map"
  MTSchema -> "schema"; MTMapVerdictSchema1 -> "lara-map-verdict@1"
  MTCore -> "core"; MTArtifact -> "artifact"
  MTNodes -> "nodes"; MTNode -> "node"
  MTLabels -> "labels"; MTEdges -> "edges"
  MTStatuses -> "statuses"; MTStatus -> "status"
  MTIn -> "in"; MTOut -> "out"; MTUndec -> "undec"
  MTGap -> "gap"; MTJustified -> "justified"
  MTContested -> "contested"; MTDefeated -> "defeated"

{-# NOINLINE mapTagTable #-}
mapTagTable :: Map.Map String MapTag
mapTagTable = Map.fromList [(mapTagToString t, t) | t <- [minBound .. maxBound]]

-- | Parse a map keyword, inverse to 'mapTagToString'. The table is derived from
-- 'mapTagToString' by enumerating 'MapTag', so a spelling collision would break
-- that inverse silently ('Map.fromList' keeps one value per key);
-- @prop_mapTagTableTotal@ (MapWireSpec) rejects collisions.
parseMapTag :: String -> Maybe MapTag
parseMapTag s = Map.lookup s mapTagTable

-- ---------------------------------------------------------------------------
-- Decode helpers
-- ---------------------------------------------------------------------------

-- | The map decoder monad: 'Either' 'MapWireError' with a 'MonadFail'
-- instance, so an arity-checked field list can be destructured directly in a
-- @do@ block. The failure path is unreachable — 'matchMapTagged' verifies
-- arity before the pattern binds. Mirrors "Lara.Wire"'s @Decode@ exactly.
newtype MapDecode a = MapDecode {runMapDecode :: Either MapWireError a}
  deriving (Functor, Applicative, Monad) via Either MapWireError

instance MonadFail MapDecode where
  fail = mwerr "decode"

mwerr :: String -> String -> MapDecode a
mwerr context message = MapDecode (Left (MapWireError context message))

mok :: a -> MapDecode a
mok = MapDecode . Right

-- | Lift a smart constructor's rejection into a located codec error.
required :: String -> String -> Maybe a -> MapDecode a
required context message = maybe (mwerr context message) mok

-- | Lift a smart constructor that /located/ its own rejection: the error it
-- built already names the section and the reason, so nothing is added here.
mfail :: MapWireError -> MapDecode a
mfail = MapDecode . Left

-- | Build a tagged list: @(tag e1 … en)@.
mtagged :: MapTag -> [SExpr] -> SExpr
mtagged t es = SList (SAtom (mapTagToString t) : es)

-- | Match a tagged list with exactly @n@ payload fields.
matchMapTagged :: String -> MapTag -> Int -> SExpr -> MapDecode [SExpr]
matchMapTagged context t arity e = case e of
  SList (SAtom k : fields)
    | parseMapTag k == Just t ->
        if length fields == arity
          then mok fields
          else
            mwerr
              context
              ( "wrong number of fields for "
                  ++ mapTagToString t
                  ++ ": expected "
                  ++ show arity
                  ++ ", got "
                  ++ show (length fields)
              )
  _ -> mwerr context ("expected (" ++ mapTagToString t ++ " …), got " ++ show e)

-- | Match a variable-arity section and return its fields.
mapSectionFields :: String -> MapTag -> SExpr -> MapDecode [SExpr]
mapSectionFields context t e = case e of
  SList (SAtom k : fields) | parseMapTag k == Just t -> mok fields
  _ -> mwerr context ("expected (" ++ mapTagToString t ++ " …), got " ++ show e)

mapAtomText :: String -> SExpr -> MapDecode String
mapAtomText _ (SAtom s) = mok s
mapAtomText context e = mwerr context ("expected an atom, got " ++ show e)

-- | A canonical decimal: no sign, no leading zeros.
mapNatText :: String -> SExpr -> MapDecode Int
mapNatText context e = do
  s <- mapAtomText context e
  case reads s :: [(Int, String)] of
    [(n, "")] | n >= 0, show n == s -> mok n
    _ -> mwerr context ("malformed natural number: " ++ show s)

-- | Match a bare atom against one keyword of a small closed alternation.
mapKeyword :: String -> [(MapTag, a)] -> SExpr -> MapDecode a
mapKeyword context alternatives e = do
  s <- mapAtomText context e
  case parseMapTag s >>= \t -> lookup t alternatives of
    Just value -> mok value
    Nothing ->
      mwerr
        context
        ( "expected one of "
            ++ show (map (mapTagToString . fst) alternatives)
            ++ ", got "
            ++ show s
        )

-- ---------------------------------------------------------------------------
-- Shared productions
-- ---------------------------------------------------------------------------

encodeAlias :: MemberAlias -> SExpr
encodeAlias = SAtom . aliasText

decodeAlias :: String -> SExpr -> MapDecode MemberAlias
decodeAlias context e = do
  text <- mapAtomText context e
  required
    context
    ("malformed member alias " ++ show text ++ ": expected nonempty [A-Za-z0-9_-]")
    (mkMemberAlias text)

encodePath :: DeclaredPath -> SExpr
encodePath = SAtom . declaredPathText

decodePath :: String -> SExpr -> MapDecode DeclaredPath
decodePath context e = do
  text <- mapAtomText context e
  required context "path must be a nonempty atom" (mkDeclaredPath text)

encodeBackends :: [(BackendId, String)] -> SExpr
encodeBackends backends =
  mtagged
    MTBackends
    [ mtagged MTBackend [SAtom backend, SAtom version]
    | (BackendId backend, version) <- backends
    ]

-- | Decode a @backends@ section: duplicate-free and strictly ascending by
-- @(id, version)@, so one backend selection has exactly one spelling.
decodeBackends :: String -> SExpr -> MapDecode [(BackendId, String)]
decodeBackends context section = do
  fields <- mapSectionFields context MTBackends section
  backends <- mapM decodeBackend fields
  if strictlyAscending backends
    then mok backends
    else
      mwerr
        context
        "backends must be duplicate-free and ascending by (id, version)"
  where
    decodeBackend e = do
      [backend, version] <- matchMapTagged context MTBackend 2 e
      (,) . BackendId <$> mapAtomText context backend <*> mapAtomText context version

encodeCoord :: Coord -> SExpr
encodeCoord coord = case coord of
  CoordWhole -> SAtom (mapTagToString MTWhole)
  CoordArg index -> mtagged MTArg [SAtom (show (argIndexInt index))]

decodeCoord :: String -> SExpr -> MapDecode Coord
decodeCoord context e = case e of
  SAtom s | parseMapTag s == Just MTWhole -> mok CoordWhole
  SList (SAtom k : _) | parseMapTag k == Just MTArg -> do
    [n] <- matchMapTagged context MTArg 1 e
    index <- mapNatText context n
    CoordArg <$> required context "argument coordinate must be non-negative" (mkArgIndex index)
  _ -> mwerr context ("expected whole or (arg NAT), got " ++ show e)

encodeRef :: MapRef -> SExpr
encodeRef ref =
  mtagged
    MTRef
    [ encodeAlias (refAlias ref)
    , SAtom (let PropId claim = refClaim ref in claim)
    , encodeCoord (refCoord ref)
    ]

decodeRef :: SExpr -> MapDecode MapRef
decodeRef = decodeRefIn "map"

-- ---------------------------------------------------------------------------
-- Manifest codec
-- ---------------------------------------------------------------------------

-- | Encode a manifest. The exact inverse of 'decodeMapManifest' for any value
-- satisfying the invariants documented on 'MapManifest' (nonempty members,
-- unique aliases, ascending duplicate-free backends, no mixed selector inside
-- an alignment, at least two references per question); a value violating one
-- encodes fine and then fails to decode. Order-preserving: members,
-- alignments, and questions print in list order.
encodeMapManifest :: MapManifest -> SExpr
encodeMapManifest manifest =
  mtagged
    MTLaraMap1
    [ mtagged
        MTPolicy
        [ SAtom (let PolicyId policy = mapPolicy manifest in policy)
        , encodePath (mapPolicyPath manifest)
        ]
    , encodeBackends (mapBackends manifest)
    , mtagged
        MTMembers
        [ mtagged MTMember [encodeAlias (memberAlias member), encodePath (memberPath member)]
        | member <- NE.toList (mapMembers manifest)
        ]
    , mtagged MTAlignments (map encodeAlignment (mapAlignments manifest))
    , mtagged MTQuestions (map encodeMapQuestion (mapQuestions manifest))
    ]

encodeAlignment :: Alignment -> SExpr
encodeAlignment alignment =
  mtagged
    MTAlignment
    [ encodeRef (alignLeft alignment)
    , encodeRef (alignRight alignment)
    , SAtom (mapTagToString (assertionTag (alignAssertion alignment)))
    , mtagged MTAuthor [SAtom (bindingAuthor binding)]
    , mtagged MTAuditStatus [SAtom (mapTagToString (auditTag (bindingAuditStatus binding)))]
    , mtagged MTRationale [SAtom (bindingRationale binding)]
    ]
  where
    binding = alignBinding alignment

assertionTag :: Assertion -> MapTag
assertionTag assertion = case assertion of
  Same -> MTSame
  Different -> MTDifferent

auditTag :: AuditStatus -> MapTag
auditTag audit = case audit of
  Unreviewed -> MTUnreviewed
  Reviewed -> MTReviewed
  Disputed -> MTDisputed

encodeMapQuestion :: MapQuestion -> SExpr
encodeMapQuestion question =
  mtagged
    MTQuestion
    [ SAtom (let QuestionId identifier = mapQuestionId question in identifier)
    , mtagged MTRefs (map encodeRef (mapQuestionRefs question))
    , mtagged MTNl [SAtom (mapQuestionNl question)]
    ]

-- | Decode a manifest from an already-parsed form.
decodeMapManifest :: SExpr -> Either MapWireError MapManifest
decodeMapManifest = runMapDecode . decodeMapManifestM

-- | Decode a manifest from its text, mapping a located S-expression parse
-- failure into a located codec error (the map analogue of
-- 'Lara.Wire.decodeCheckInputFile'). Exactly one top-level form is accepted.
decodeMapManifestText :: String -> Either MapWireError MapManifest
decodeMapManifestText text = case parseSExpr text of
  Left (ParseError line column message) ->
    Left (MapWireError ("line " ++ show line ++ ", column " ++ show column) message)
  Right value -> decodeMapManifest value

decodeMapManifestM :: SExpr -> MapDecode MapManifest
decodeMapManifestM value = do
  [policySection, backendsSection, membersSection, alignmentsSection, questionsSection] <-
    matchMapTagged "map manifest" MTLaraMap1 5 value
  [policy, policyPath] <- matchMapTagged "map policy" MTPolicy 2 policySection
  policyId <- PolicyId <$> mapAtomText "map policy" policy
  declaredPolicyPath <- decodePath "map policy" policyPath
  backends <- decodeBackends "map backends" backendsSection
  members <- decodeMembers membersSection
  alignments <-
    mapSectionFields "map alignments" MTAlignments alignmentsSection
      >>= mapM decodeAlignment
  questions <-
    mapSectionFields "map questions" MTQuestions questionsSection
      >>= mapM decodeMapQuestion
  -- The record is not assembled here. 'mkMapManifest' owns every invariant a
  -- 'MapManifest' promises, and routing the decoder through it is what keeps the
  -- two from drifting: a check added there is a check this door gains, and the
  -- messages cannot diverge because there is only one copy of each. The
  -- section-level checks above still run first, so a defect inside a section is
  -- still reported against that section.
  either mfail mok
    (mkMapManifest policyId declaredPolicyPath backends members alignments questions)

decodeMembers :: SExpr -> MapDecode (NonEmpty MapMember)
decodeMembers section = do
  fields <- mapSectionFields context MTMembers section
  members <- mapM decodeMember fields
  case NE.nonEmpty members of
    Nothing -> mwerr context "a map declares at least one member"
    Just nonEmptyMembers -> case firstDuplicate (map memberAlias members) of
      Just duplicate -> mwerr context ("duplicate member alias " ++ aliasText duplicate)
      Nothing -> mok nonEmptyMembers
  where
    context = "map members"
    decodeMember e = do
      [alias, path] <- matchMapTagged context MTMember 2 e
      MapMember <$> decodeAlias context alias <*> decodePath context path

decodeAlignment :: SExpr -> MapDecode Alignment
decodeAlignment = MapDecode . decodeAlignmentIn "map"

-- | The alignment production, decoded under a caller-supplied context.
--
-- __One grammar, one codec.__ The manifest and the parity envelope both carry
-- alignments, and they carry the /same/ production: @alignment@, @ref@,
-- @whole@, @arg@, @same@, @different@, @author@, @audit-status@, @rationale@,
-- and the three audit statuses — twelve spellings. They used to be encoded and
-- decoded twice, against two tag tables, with a within-table collision test on
-- each and nothing asserting the two tables agreed. The @MapTag@ \/ @EnvTag@
-- split is right for words each grammar owns; it is wrong here, because this is
-- not two grammars reusing a word but two grammars sharing a production. When
-- the manifest's alignment grammar moved, the envelope kept the old spelling
-- with no compile error, and the Lean parity harness then compared against a
-- production the manifest no longer emitted.
--
-- Only the diagnostic /context/ differs between the two doors, so it is a
-- parameter: the manifest says @map alignment@ and the envelope says
-- @map check-input alignment@, and an operator still learns which door refused.
--
-- Returns 'Either' rather than either door's decode monad, because the two doors
-- have different ones ("Lara.Map.Wire".@MapDecode@ and
-- "Lara.Map.Driver".@EnvDecode@); each lifts it in one line.
decodeAlignmentIn :: String -> SExpr -> Either MapWireError Alignment
decodeAlignmentIn door e = runMapDecode $ do
  [left, right, assertion, author, audit, rationale] <-
    matchMapTagged context MTAlignment 6 e
  leftRef <- decodeRefIn door left
  rightRef <- decodeRefIn door right
  declared <- mapKeyword context [(MTSame, Same), (MTDifferent, Different)] assertion
  [authorText] <- matchMapTagged context MTAuthor 1 author
  [auditText] <- matchMapTagged context MTAuditStatus 1 audit
  [rationaleText] <- matchMapTagged context MTRationale 1 rationale
  binding <-
    Binding
      <$> mapAtomText context authorText
      <*> mapAtomText context rationaleText
      <*> mapKeyword
        context
        [(MTUnreviewed, Unreviewed), (MTReviewed, Reviewed), (MTDisputed, Disputed)]
        auditText
  if sameSelectorKind (refCoord leftRef) (refCoord rightRef)
    then
      mok
        Alignment
          { alignLeft = leftRef
          , alignRight = rightRef
          , alignAssertion = declared
          , alignBinding = binding
          }
    else
      mwerr
        context
        "an alignment's two coordinates must both be whole or both be (arg n)"
  where
    context = door ++ " alignment"

-- | The @ref@ production, under the same door prefix its alignment uses.
decodeRefIn :: String -> SExpr -> MapDecode MapRef
decodeRefIn door e = do
  [alias, claim, coord] <- matchMapTagged context MTRef 3 e
  MapRef
    <$> decodeAlias context alias
    <*> (PropId <$> mapAtomText context claim)
    <*> decodeCoord (door ++ " coord") coord
  where
    context = door ++ " ref"

decodeMapQuestion :: SExpr -> MapDecode MapQuestion
decodeMapQuestion e = do
  [identifier, refs, nl] <- matchMapTagged context MTQuestion 3 e
  questionId <- QuestionId <$> mapAtomText context identifier
  references <- mapSectionFields context MTRefs refs >>= mapM decodeRef
  [nlText] <- matchMapTagged context MTNl 1 nl
  text <- mapAtomText context nlText
  if length references >= 2
    then mok (MapQuestion questionId references text)
    else mwerr context "a map question relates at least two references"
  where
    context = "map question"

-- ---------------------------------------------------------------------------
-- Composite verdict codec
-- ---------------------------------------------------------------------------

-- | Encode a composite verdict. The exact inverse of 'decodeMapVerdict' for any
-- value satisfying the invariants documented on 'MapVerdict' (nonempty members
-- with unique aliases, ascending duplicate-free backends, labels covering
-- @0 .. n-1@, strictly ascending in-range edges, and unique node handles over
-- declared aliases whose indices cover exactly the labelled arguments); a value
-- violating one encodes fine and then fails to decode. Canonical: equal values
-- print equal bytes, and every section prints in list order — the driver owns
-- the ordering, the codec only preserves it.
encodeMapVerdict :: MapVerdict -> SExpr
encodeMapVerdict verdict =
  mtagged
    MTMapVerdict1
    [ mtagged MTScope [SAtom (mapTagToString (scopeTag (mvScope verdict)))]
    , mtagged MTSchema [SAtom (mapTagToString (schemaTag (mvSchema verdict)))]
    , mtagged MTCore [SAtom (coreVersionText (mvCore verdict))]
    , mtagged MTPolicy [SAtom (let PolicyId policy = mvPolicy verdict in policy)]
    , encodeBackends (mvBackends verdict)
    , mtagged MTMembers (map encodeMemberRecord (NE.toList (mvMembers verdict)))
    , mtagged MTNodes (map encodeMapNode (mvNodes verdict))
    , mtagged
        MTLabels
        [ SList [SAtom (show (nodeIndexInt index)), SAtom (mapTagToString (labelTag label))]
        | (index, label) <- mvLabels verdict
        ]
    , mtagged
        MTEdges
        [ SList [SAtom (show (nodeIndexInt source)), SAtom (show (nodeIndexInt target))]
        | (source, target) <- mvEdges verdict
        ]
    , mtagged MTStatuses (map encodeMapStatus (mvStatuses verdict))
    ]

scopeTag :: MapScope -> MapTag
scopeTag ScopeMap = MTMap

schemaTag :: MapSchema -> MapTag
schemaTag MapVerdictSchemaV1 = MTMapVerdictSchema1

labelTag :: Label -> MapTag
labelTag label = case label of
  LIn -> MTIn
  LOut -> MTOut
  LUndec -> MTUndec

statusTag :: Status -> MapTag
statusTag status = case status of
  Gap -> MTGap
  Justified -> MTJustified
  Contested -> MTContested
  Defeated -> MTDefeated

encodeMemberRecord :: MemberRecord -> SExpr
encodeMemberRecord record =
  mtagged
    MTMember
    [ encodeAlias (mrAlias record)
    , encodePath (mrPath record)
    , mtagged MTArtifact [SAtom (let Digest digest = mrArtifact record in digest)]
    ]

encodeMapNode :: MapNode -> SExpr
encodeMapNode node =
  mtagged
    MTNode
    [ encodeAlias (mnAlias node)
    , SAtom (let ArgId argument = mnArg node in argument)
    , SAtom (show (nodeIndexInt (mnIndex node)))
    ]

encodeMapStatus :: MapStatus -> SExpr
encodeMapStatus status =
  mtagged
    MTStatus
    [ encodeAlias (msAlias status)
    , SAtom (let PropId claim = msClaim status in claim)
    , encodeAtom (msAtom status)
    , SAtom (mapTagToString (statusTag (msStatus status)))
    ]

-- | Decode a composite verdict, including the self-consistency invariants a
-- terminal artifact must satisfy (see the module header).
decodeMapVerdict :: SExpr -> Either MapWireError MapVerdict
decodeMapVerdict = runMapDecode . decodeMapVerdictM

decodeMapVerdictM :: SExpr -> MapDecode MapVerdict
decodeMapVerdictM value = do
  [ scopeSection
    , schemaSection
    , coreSection
    , policySection
    , backendsSection
    , membersSection
    , nodesSection
    , labelsSection
    , edgesSection
    , statusesSection
    ] <-
    matchMapTagged context MTMapVerdict1 10 value
  [scope] <- matchMapTagged "map verdict scope" MTScope 1 scopeSection
  scopeValue <- mapKeyword "map verdict scope" [(MTMap, ScopeMap)] scope
  [schema] <- matchMapTagged "map verdict schema" MTSchema 1 schemaSection
  schemaValue <-
    mapKeyword "map verdict schema" [(MTMapVerdictSchema1, MapVerdictSchemaV1)] schema
  [core] <- matchMapTagged "map verdict core" MTCore 1 coreSection
  coreValue <- decodeCoreVersion core
  [policy] <- matchMapTagged "map verdict policy" MTPolicy 1 policySection
  policyId <- PolicyId <$> mapAtomText "map verdict policy" policy
  backends <- decodeBackends "map verdict backends" backendsSection
  members <- decodeMemberRecords membersSection
  let declared = Set.fromList (map mrAlias (NE.toList members))
  labels <- decodeLabels labelsSection
  let nodeCount = length labels
  nodes <- decodeNodes declared nodeCount nodesSection
  edges <- decodeEdges nodeCount edgesSection
  statuses <- decodeStatuses declared statusesSection
  mok
    MapVerdict
      { mvScope = scopeValue
      , mvSchema = schemaValue
      , mvCore = coreValue
      , mvPolicy = policyId
      , mvBackends = backends
      , mvMembers = members
      , mvNodes = nodes
      , mvLabels = labels
      , mvEdges = edges
      , mvStatuses = statuses
      }
  where
    context = "map verdict"

decodeCoreVersion :: SExpr -> MapDecode CoreVersion
decodeCoreVersion e = do
  text <- mapAtomText context e
  if text == coreVersionText LaraCoreV02
    then mok LaraCoreV02
    else mwerr context ("expected " ++ coreVersionText LaraCoreV02 ++ ", got " ++ show text)
  where
    context = "map verdict core"

decodeMemberRecords :: SExpr -> MapDecode (NonEmpty MemberRecord)
decodeMemberRecords section = do
  fields <- mapSectionFields context MTMembers section
  members <- mapM decodeMemberRecord fields
  case NE.nonEmpty members of
    Nothing -> mwerr context "a map verdict reports at least one member"
    Just nonEmptyMembers -> case firstDuplicate (map mrAlias members) of
      Just duplicate -> mwerr context ("duplicate member alias " ++ aliasText duplicate)
      Nothing -> mok nonEmptyMembers
  where
    context = "map verdict members"
    decodeMemberRecord e = do
      [alias, path, artifact] <- matchMapTagged context MTMember 3 e
      [digest] <- matchMapTagged context MTArtifact 1 artifact
      MemberRecord
        <$> decodeAlias context alias
        <*> decodePath context path
        <*> (Digest <$> mapAtomText context digest)

-- | Labels cover every argument of the linked unit exactly once, in ascending
-- index order — so the section's own bytes pin @n@.
decodeLabels :: SExpr -> MapDecode [(NodeIndex, Label)]
decodeLabels section = do
  fields <- mapSectionFields context MTLabels section
  labels <- mapM decodeLabel fields
  if map (nodeIndexInt . fst) labels == [0 .. length labels - 1]
    then mok labels
    else mwerr context "labels must cover 0..n-1 in ascending order"
  where
    context = "map verdict labels"
    decodeLabel e = case e of
      SList [index, label] ->
        (,)
          <$> decodeNodeIndex context index
          <*> mapKeyword context [(MTIn, LIn), (MTOut, LOut), (MTUndec, LUndec)] label
      _ -> mwerr context ("expected (INDEX LABEL), got " ++ show e)

-- | The provenance table: one entry per @(member alias, local argument id)@ any
-- member declared, each naming the linked index its term became.
--
-- Three conditions, and the third is the one worth explaining. Each handle
-- occurs once, because a handle is a /name/ and a repeated one would give a
-- reader two answers to one question. Each index names a labelled argument,
-- because an index that does not is not a position in this framework. And the
-- indices __cover every labelled argument__: a linked argument exists precisely
-- because some member declared its support term, so a labelled index with no
-- handle describes an argument that arose from nobody — which no producer can
-- emit and no consumer could attribute.
--
-- Coverage was deliberately left out when this codec landed, because asserting
-- it before anything produced a node table would have pinned a shape no
-- producer had had to satisfy. @Lara.Map.Driver@ is that producer now, and
-- every verdict it emits satisfies it.
decodeNodes :: Set.Set MemberAlias -> Int -> SExpr -> MapDecode [MapNode]
decodeNodes declared nodeCount section = do
  fields <- mapSectionFields context MTNodes section
  nodes <- mapM decodeNode fields
  case firstDuplicate [(mnAlias node, mnArg node) | node <- nodes] of
    Just (alias, ArgId argument) ->
      mwerr
        context
        ("duplicate argument handle " ++ qualifiedDisplay (qualifyId alias argument))
    Nothing
      | Set.fromList (map (nodeIndexInt . mnIndex) nodes)
          == Set.fromList [0 .. nodeCount - 1] ->
          mok nodes
      | otherwise ->
          mwerr
            context
            ( "nodes must name every labelled argument: "
                ++ show nodeCount
                ++ " labelled, "
                ++ show (Set.size (Set.fromList (map (nodeIndexInt . mnIndex) nodes)))
                ++ " named"
            )
  where
    context = "map verdict nodes"
    decodeNode e = do
      [alias, argument, index] <- matchMapTagged context MTNode 3 e
      aliasValue <- decodeAlias context alias
      if aliasValue `Set.member` declared
        then
          MapNode aliasValue . ArgId
            <$> mapAtomText context argument
            <*> decodeBoundedIndex context nodeCount index
        else mwerr context ("undeclared member alias " ++ aliasText aliasValue)

decodeEdges :: Int -> SExpr -> MapDecode [(NodeIndex, NodeIndex)]
decodeEdges nodeCount section = do
  fields <- mapSectionFields context MTEdges section
  edges <- mapM decodeEdge fields
  if strictlyAscending edges
    then mok edges
    else mwerr context "edges must be duplicate-free and ascending by (source, target)"
  where
    context = "map verdict edges"
    decodeEdge e = case e of
      SList [source, target] ->
        (,)
          <$> decodeBoundedIndex context nodeCount source
          <*> decodeBoundedIndex context nodeCount target
      _ -> mwerr context ("expected (SOURCE TARGET), got " ++ show e)

-- | The per-claim report, refusing a repeated @(alias, claim)@ handle.
--
-- The duplicate check mirrors 'decodeNodes'\', and for the reason the module
-- header gives: a composite verdict is a __terminal artifact__, so its decoder
-- settles everything its own bytes determine rather than leaving a consumer to
-- discover it. @(alias, claim name)@ is the handle a reader resolves a status
-- by; two rows under one handle make @lookup@ silently first-wins, and the two
-- rows may carry different statuses. 'MBDuplicateClaim' refuses a /member/ with
-- a repeated claim name for exactly this reason, so a verdict carrying one
-- would contradict the rule its own inputs were held to.
--
-- No producer here can emit such a verdict — this closes a boundary-strictness
-- gap, not a live defect.
decodeStatuses :: Set.Set MemberAlias -> SExpr -> MapDecode [MapStatus]
decodeStatuses declared section = do
  fields <- mapSectionFields context MTStatuses section
  statuses <- mapM decodeStatus fields
  case firstDuplicate [(msAlias status, msClaim status) | status <- statuses] of
    Just (alias, PropId claim) ->
      mwerr
        context
        ("duplicate claim handle " ++ qualifiedDisplay (qualifyId alias claim))
    Nothing -> mok statuses
  where
    context = "map verdict statuses"
    decodeStatus e = do
      [alias, claim, atom, status] <- matchMapTagged context MTStatus 4 e
      aliasValue <- decodeAlias context alias
      if aliasValue `Set.member` declared
        then
          MapStatus aliasValue . PropId
            <$> mapAtomText context claim
            <*> decodeMapAtom context atom
            <*> mapKeyword
              context
              [ (MTGap, Gap)
              , (MTJustified, Justified)
              , (MTContested, Contested)
              , (MTDefeated, Defeated)
              ]
              status
        else mwerr context ("undeclared member alias " ++ aliasText aliasValue)

-- | Read a proposition in @lara-core\@0.2@'s @\<atom\>@ form, relabelling the
-- core codec's failure with the map position that asked for it.
decodeMapAtom :: String -> SExpr -> MapDecode Prop
decodeMapAtom context e = case decodeAtomSExpr e of
  Left (WireError atomContext message) ->
    mwerr (context ++ ": " ++ atomContext) message
  Right proposition -> mok proposition

decodeNodeIndex :: String -> SExpr -> MapDecode NodeIndex
decodeNodeIndex context e = do
  index <- mapNatText context e
  required context "index must be non-negative" (mkNodeIndex index)

-- | A linked-unit index that must name a labelled argument.
decodeBoundedIndex :: String -> Int -> SExpr -> MapDecode NodeIndex
decodeBoundedIndex context nodeCount e = do
  index <- decodeNodeIndex context e
  if nodeIndexInt index < nodeCount
    then mok index
    else
      mwerr
        context
        ( "index "
            ++ show (nodeIndexInt index)
            ++ " names no labelled argument (there are "
            ++ show nodeCount
            ++ ")"
        )
