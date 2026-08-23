-- | Well-formedness tests for the flat backends' premise-reference schemas
-- ('Lara.Strict.Cell.SlotSchema') and conformance tests for the lowering
-- pass over them ('Lara.Elaborate.CertSlots.lowerCertPayload'): each declared
-- schema matches its backend's wire grammar byte-for-byte (identity, head
-- keyword, arity, reference positions), every declared reference slot sits
-- inside the payload arity, and the lowering rewrites exactly the symbolic
-- names at declared reference positions while passing every other payload
-- through byte-identical. Conformance evidence for the presentation layer
-- only — the schemas introduce no new wire spellings, so these tests pin
-- that the declared values agree with each backend's own tag table and
-- identity, and that no lowered payload differs from what an author could
-- have written numerically by hand.
--
-- The second half drives the same pass through a real @parse + elaborate@
-- (@lara-syntax\@0.6@, #105), where the resolver is the elaborator's own name
-- scope rather than a fixture function: an authored certificate that cites its
-- premises by source name must elaborate to /exactly/ the 'Lara.AST.Unit' the
-- numeric spelling produces, in both the explicit and the inferred spelling,
-- and every way a name can fail must be rejected with its own located
-- 'Lara.Elaborate.Internal.ElabError'.
--
-- The third part carries the pass through the rest of the pipeline (#105's
-- verification target verbatim): symbolic and numeric twins encode to
-- byte-identical wire units and byte-identical verdicts on both schema'd
-- backends, the lowered unit replays and a tampered payload byte is an R13
-- rejection at the certificate replay gate, an @nd\@1@ payload reaches the
-- wire untouched, and the authored symbolic spelling survives the printer
-- round-trip (D7: zero parser changes).
module CertSlotsSpec (certSlotsSpecProps) where

import Data.List (isInfixOf, nub, sort)
import Test.QuickCheck

import Lara.Admission (renderAdmissionRejection)
import Lara.AST
  ( Arg (..)
  , ArgId (..)
  , ArgInstantiation (..)
  , Assurance (..)
  , Cert (..)
  , Decl (..)
  , Label (..)
  , LeafId (..)
  , Policy (..)
  , Program (..)
  , RejectClass (..)
  , Rejection (..)
  , RuleId (..)
  , Status (..)
  , SupportTerm (..)
  , TheoryDigest (..)
  , Unit (..)
  )
import qualified Lara.AST as AST
import Lara.Driver (runCheck)
import Lara.Elaborate
  ( PreparedSource (..)
  , prepareSource
  , renderSourceInvalid
  , runSourceCheck
  , sourceResultVerdict
  )
import Lara.Elaborate.CertSlots (SlotRefError (..), lowerCertPayload, slotSchemas)
import Lara.Elaborate.Internal (ElabError (..), elabErrorMessage, elaborate, registryOf)
import Lara.Replay
  ( CheckInput
  , CoreVersion (..)
  , ReplayError
  , mkCheckInput
  , mkReplayId
  , replayErrorMessage
  , runtimeReplayFailure
  )
import Lara.Strict (BackendId (..), SExpr (..))
import Lara.Strict.Cell (SlotSchema (..), parseCanonicalNat)
import qualified Lara.Strict.Ord as Ord
import qualified Lara.Strict.RA as RA
import Lara.Syntax (parsePolicy, parseProgram, printProgram)
import Lara.Wire
  ( Outcome (..)
  , PublicStatus (..)
  , Verdict (..)
  , encodeUnit
  , encodeVerdict
  , printSExpr
  )

-- | @ord\@1@ declares @(ordcmp (prem N) (prem M))@: arity 2, both positions
-- premise references.
prop_ordSchemaMatchesWireGrammar :: Bool
prop_ordSchemaMatchesWireGrammar =
  ssBackend Ord.slotSchema == BackendId {backendName = "ord", backendVersion = 1}
    && ssHead Ord.slotSchema == "ordcmp"
    && ssArity Ord.slotSchema == 2
    && ssRefSlots Ord.slotSchema == [0, 1]

-- | @ra\@1@ declares @(radrop (prem N) (prem M) (frac P Q))@: arity 3, the
-- first two positions premise references, the witness fraction untouched.
prop_raSchemaMatchesWireGrammar :: Bool
prop_raSchemaMatchesWireGrammar =
  ssBackend RA.slotSchema == BackendId {backendName = "ra", backendVersion = 1}
    && ssHead RA.slotSchema == "radrop"
    && ssArity RA.slotSchema == 3
    && ssRefSlots RA.slotSchema == [0, 1]

-- | Internal coherence: no schema declares a reference position outside its
-- own payload arity. Runs over the registry itself so any future schema is
-- covered automatically.
prop_refSlotsInsideArity :: Bool
prop_refSlotsInsideArity =
  all
    (\s -> all (< ssArity s) (ssRefSlots s))
    slotSchemas

-- | Internal coherence: schema keys are pairwise distinct. 'matchSchema'
-- requires a unique @(backend, head, arity)@ match, so a duplicate entry
-- would silently degrade to no-match (pass-through or dead-wire) instead of
-- surfacing the table bug — this pins it at the source.
prop_schemaKeysDistinct :: Bool
prop_schemaKeysDistinct =
  let keys = [(ssBackend s, ssHead s, ssArity s) | s <- slotSchemas]
   in length keys == length (nub keys)

-- ---------------------------------------------------------------------------
-- Lowering fixtures
-- ---------------------------------------------------------------------------

-- | The fixed test resolver standing in for the elaborator's name scope:
-- two premises named @e1@\/@e2@ at slots 0\/1, plus one name per resolver
-- failure mode.
res :: String -> Either SlotRefError Int
res "e1" = Right 0
res "e2" = Right 1
res "dup" = Left (SlotNameMultiSlot 0 1 False)
res "off" = Left SlotNameNotAPremise
res "both" = Left SlotNameAmbiguous
res _ = Left SlotNameUnresolved

-- | A presentation certificate over the given backend name\/version, with a
-- fixed theory digest, as the elaborator holds it after parsing.
certOver :: String -> Int -> SExpr -> Cert
certOver name version payload =
  Cert
    { certBackend = AST.BackendId name
    , certVersion = version
    , certTheory = TheoryDigest "sha256:t"
    , certPayload = payload
    }

ordCert :: SExpr -> Cert
ordCert = certOver "ord" 1

raCert :: SExpr -> Cert
raCert = certOver "ra" 1

ndCert :: SExpr -> Cert
ndCert = certOver "nd" 1

prem :: String -> SExpr
prem s = SList [SAtom "prem", SAtom s]

ordcmp :: SExpr -> SExpr -> SExpr
ordcmp a b = SList [SAtom "ordcmp", a, b]

-- ---------------------------------------------------------------------------
-- Lowering: symbolic references at declared positions
-- ---------------------------------------------------------------------------
--
-- Conformance vectors mirrored in lean/Lara/CertSlots.lean (#guard,
-- build-time). Most use the fixed resolver e1 -> 0, e2 -> 1, else fail; V10
-- uses a resolver for the legal non-ASCII source identifier é1. The Lean
-- mirror collapses every failure to none, while the props here additionally
-- pin WHICH 'SlotRefError' each failing vector reports:
--   V1 symbolic ord              -> prop_lowersSymbolicOrdRefs
--   V2 mixed symbolic/numeric    -> prop_acceptsMixedPositions
--   V3 ra with frac witness      -> prop_lowersRaRefsAroundWitness
--   V4 nd@1 pass-through         -> prop_passesMismatchesWithoutSymbolsThrough (nd payload)
--   V5 wrong-arity pass-through  -> prop_passesMismatchesWithoutSymbolsThrough (arity-1 ordcmp)
--   V6 numeric identity          -> prop_leavesNumericPayloadsUntouched
--   V7 dead-wire mismatch        -> prop_rejectsSymbolsInMismatchedPayloads (arity-1 + "e1")
--   V8 resolver failure          -> prop_reportsResolverFailures ("nope")
--   V9 non-canonical numeral     -> prop_rejectsNonCanonicalNumerals ("007")
--   V9b typo early-out is resolver-independent -> same prop: the reported
--       SlotNonCanonicalNumeral (not res's SlotNameUnresolved) proves the
--       resolver was never consulted; Lean pins it with an all-resolving rho
--   V10 Unicode identifier       -> prop_lowersUnicodeIdentifierRef
--   V11 invalid identifier starts -> prop_rejectsNonCanonicalNumerals ("#x", ".x")

-- | @(ordcmp (prem e1) (prem e2))@ lowers to @(ordcmp (prem 0) (prem 1))@.
prop_lowersSymbolicOrdRefs :: Bool
prop_lowersSymbolicOrdRefs =
  lowerCertPayload res (ordCert (ordcmp (prem "e1") (prem "e2")))
    == Right (ordCert (ordcmp (prem "0") (prem "1")))

-- | A symbolic and a numeric reference may sit side by side.
prop_acceptsMixedPositions :: Bool
prop_acceptsMixedPositions =
  lowerCertPayload res (ordCert (ordcmp (prem "e1") (prem "1")))
    == Right (ordCert (ordcmp (prem "0") (prem "1")))

-- | A legal non-ASCII source identifier reaches the resolver and lowers just
-- like an ASCII identifier. This pins Haskell's Unicode-aware lexical boundary
-- against Lean's numeric-start model.
prop_lowersUnicodeIdentifierRef :: Bool
prop_lowersUnicodeIdentifierRef =
  lowerCertPayload unicodeRes (ordCert (ordcmp (prem "é1") (prem "1")))
    == Right (ordCert (ordcmp (prem "0") (prem "1")))
  where
    unicodeRes "é1" = Right 0
    unicodeRes _ = Left SlotNameUnresolved

-- | An already-numeric payload is untouched.
prop_leavesNumericPayloadsUntouched :: Bool
prop_leavesNumericPayloadsUntouched =
  lowerCertPayload res c == Right c
  where
    c = ordCert (ordcmp (prem "0") (prem "1"))

-- | Any symbolic slot atom that cannot be a source identifier is a malformed
-- numeral rather than a name: it gets the dedicated error without consulting
-- the resolver.
prop_rejectsNonCanonicalNumerals :: Bool
prop_rejectsNonCanonicalNumerals =
  all
    ( \s ->
        lowerCertPayload res (ordCert (ordcmp (prem s) (prem "e2")))
          == Left (s, SlotNonCanonicalNumeral)
    )
    ["007", "00", "-1", "+1", "1.0", "0x10", "#x", ".x"]

-- | Every resolver failure surfaces with the offending name attached.
prop_reportsResolverFailures :: Bool
prop_reportsResolverFailures =
  all
    ( \(name, err) ->
        lowerCertPayload res (ordCert (ordcmp (prem name) (prem "e2")))
          == Left (name, err)
    )
    [ ("nope", SlotNameUnresolved)
    , ("both", SlotNameAmbiguous)
    , ("off", SlotNameNotAPremise)
    , ("dup", SlotNameMultiSlot 0 1 False)
    ]

-- | @ra\@1@'s witness fraction is not a reference position: it passes
-- through while the two references lower. Even a symbolic-looking
-- @(prem e1)@ there remains backend-owned and is not rewritten.
prop_lowersRaRefsAroundWitness :: Bool
prop_lowersRaRefsAroundWitness =
  lowerCertPayload res (raCert (radrop (prem "e1") (prem "e2") frac))
    == Right (raCert (radrop (prem "0") (prem "1") frac))
    && lowerCertPayload res symbolicWitness == Right symbolicWitness
  where
    radrop a b witnessExpr = SList [SAtom "radrop", a, b, witnessExpr]
    frac = SList [SAtom "frac", SAtom "119", SAtom "500"]
    symbolicWitness = raCert (radrop (prem "0") (prem "1") (prem "e1"))

-- ---------------------------------------------------------------------------
-- Lowering: pass-through and the dead-wire rule
-- ---------------------------------------------------------------------------

-- | Schema-less backends, unknown backend versions, and symbolic-free
-- schema-mismatched payloads pass through byte-identical. Version identity is
-- part of the schema key: neither numeric nor symbolic @ord\@2@ payloads may
-- inherit @ord\@1@ lowering.
prop_passesMismatchesWithoutSymbolsThrough :: Bool
prop_passesMismatchesWithoutSymbolsThrough =
  all
    (\c -> lowerCertPayload res c == Right c)
    [ ndCert (SList [SAtom "app", SList [SAtom "hyp", SAtom "0"], SList [SAtom "hyp", SAtom "1"]])
    , ordCert (SList [SAtom "ordcmp2", prem "0", prem "1"])
    , ordCert (SList [SAtom "ordcmp", prem "0"])
    , ordCert (SAtom "opaque")
    , certOver "ord" 2 (ordcmp (prem "0") (prem "1"))
    , certOver "ord" 2 (ordcmp (prem "e1") (prem "e2"))
    ]

-- | A symbolic name is never valid in a declared reference position or in a
-- schema-mismatched payload of a schema'd backend, so the latter is rejected
-- rather than passed through. A schema-less backend still passes through even
-- around a @(prem x)@ spelling.
prop_rejectsSymbolsInMismatchedPayloads :: Bool
prop_rejectsSymbolsInMismatchedPayloads =
  lowerCertPayload res (ordCert (SList [SAtom "ordcmp2", prem "e1", prem "e2"]))
    == Left ("e1", SlotSchemaMismatch)
    && lowerCertPayload res (ordCert (SList [SAtom "ordcmp", prem "e1"]))
      == Left ("e1", SlotSchemaMismatch)
    && lowerCertPayload res (ordCert (SList [SAtom "ordcmp2", SList [SAtom "wrap", prem "e9"]]))
      == Left ("e9", SlotSchemaMismatch)
    && lowerCertPayload res nonPremMismatch == Right nonPremMismatch
    && lowerCertPayload res ndPrem == Right ndPrem
  where
    nonPremMismatch = ordCert (SList [SAtom "ordcmp2", SList [SAtom "theory", SAtom "e1"]])
    ndPrem = ndCert (SList [SAtom "app", prem "x"])

-- | A non-@(prem …)@ node at a reference position is left for the backend,
-- including a list with the same two-atom shape but a different head.
prop_leavesNonPremNodeAtRefPosition :: Bool
prop_leavesNonPremNodeAtRefPosition =
  all (\c -> lowerCertPayload res c == Right c) [atomNode, listNode]
  where
    atomNode = ordCert (ordcmp (SAtom "junk") (prem "1"))
    listNode = ordCert (ordcmp (SList [SAtom "theory", SAtom "e1"]) (prem "1"))

-- ---------------------------------------------------------------------------
-- Lowering: the identity property on symbolic-free payloads
-- ---------------------------------------------------------------------------

-- | Payloads of depth at most 3 over a small atom pool covering the @prem@
-- keyword, both schema'd heads, canonical and non-canonical numerals, and a
-- plain name — enough to hit schema matches, mismatches, and near-misses.
boundedSExpr :: Gen SExpr
boundedSExpr = go (3 :: Int)
  where
    atom = elements ["prem", "ordcmp", "radrop", "frac", "0", "1", "2", "007", "x"]
    go :: Int -> Gen SExpr
    go 0 = SAtom <$> atom
    go d =
      oneof
        [ SAtom <$> atom
        , do
            n <- choose (0, 3 :: Int)
            SList <$> vectorOf n (go (d - 1))
        ]

-- | Test-local generic scan: no @(prem s)@ subtree with non-canonical @s@
-- anywhere. Deliberately not a mirror of the implementation's
-- schema-position walk.
noSymbolicRef :: SExpr -> Bool
noSymbolicRef (SAtom _) = True
noSymbolicRef (SList [SAtom "prem", SAtom s])
  | Nothing <- parseCanonicalNat s = False
noSymbolicRef (SList es) = all noSymbolicRef es

-- | On any payload with no symbolic reference anywhere, lowering is the
-- identity — whether or not the payload matches a schema.
prop_identityOnSymbolicFreePayloads :: Property
prop_identityOnSymbolicFreePayloads =
  forAll boundedSExpr $ \p ->
    noSymbolicRef p ==>
      let c = certOver "ord" 1 p
       in lowerCertPayload res c === Right c

-- ---------------------------------------------------------------------------
-- Elaboration fixtures: named slots through a real parse + elaborate
-- ---------------------------------------------------------------------------

-- | A policy whose strict rules are certified by @ord\@1@, small but shaped to
-- reach every resolver verdict: 'pair' takes two premises matched by distinct
-- leaves, 'twin' takes the /same/ premise pattern twice (so one leaf occupies
-- two slots), 'select' produces a prior argument for 'promote' to cite, and
-- @e3@ is a declared leaf that no instance below admits.
--
-- Every rule but 'plain', 'plainTwin', the two ambiguous slots of
-- 'partialTwin', and the final ambiguous slot of 'partialTriple' /labels/
-- its premises
-- (@lara-syntax\@0.8@, #131), so
-- the same fixture reaches the third name class: 'pair' for the twin property,
-- 'twin' for the multi-slot case only labels can cite, and 'select'\/'promote'
-- for the nested-instance scoping pin (a label belongs to the rule of the
-- instance that cites it, never to an enclosing one). 'plain' is 'pair' with
-- the labels removed, and is the pre-@0.8@ control: 'premiseLabelIndex' is
-- 'Nothing' for every name there, so the resolver must behave exactly as it
-- did at @0.6@ — the shape of every frozen policy in the corpus.
certPolicySource :: String
certPolicySource =
  unlines
    [ "policy cert-slots-v1"
    , "sort System"
    , "con sys_a : System"
    , "con sys_b : System"
    , "pred alpha(System, Num)"
    , "pred beta(System, Num)"
    , "pred selected(System, Num)"
    , "pred paired(System, Num)"
    , "pred twinned(System, Num)"
    , "rule select(X, V)"
    , "  mode = strict"
    , "  premises = [ src: alpha(X, V) ]"
    , "  conclusion = selected(X, V)"
    , "  allow-trusted = true"
    , "  certifiers = []"
    , "rule pair(X, V)"
    , "  mode = strict"
    , "  premises = [ base: alpha(X, V), new: beta(X, V) ]"
    , "  conclusion = paired(X, V)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:cert-slots-theory-0) ]"
    , "rule promote(X, V)"
    , "  mode = strict"
    , "  premises = [ chosen: selected(X, V), other: beta(X, V) ]"
    , "  conclusion = paired(X, V)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:cert-slots-theory-0) ]"
    , "rule plain(X, V)"
    , "  mode = strict"
    , "  premises = [ alpha(X, V), beta(X, V) ]"
    , "  conclusion = paired(X, V)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:cert-slots-theory-0) ]"
    , "rule plainTwin(X, V)"
    , "  mode = strict"
    , "  premises = [ alpha(X, V), alpha(X, V) ]"
    , "  conclusion = twinned(X, V)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:cert-slots-theory-0) ]"
    , "rule twin(X, V)"
    , "  mode = strict"
    , "  premises = [ left: alpha(X, V), right: alpha(X, V) ]"
    , "  conclusion = twinned(X, V)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:cert-slots-theory-0) ]"
    , "rule partialTwin(X, V)"
    , "  mode = strict"
    , "  premises = [ alpha(X, V), alpha(X, V), repair: beta(X, V) ]"
    , "  conclusion = twinned(X, V)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:cert-slots-theory-0) ]"
    , "rule partialTriple(X, V)"
    , "  mode = strict"
    , "  premises = [ first: alpha(X, V), second: alpha(X, V), alpha(X, V), repair: beta(X, V) ]"
    , "  conclusion = twinned(X, V)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:cert-slots-theory-0) ]"
    ]

-- | The fixture program with the supplied @arg@ (and any extra declaration)
-- block spliced in. @e1@\/@e2@ are the two premises of a @pair(sys_a, 0.74)@
-- instance; @e3@ is declared but admitted by no instance below.
certProgramSource :: [String] -> String
certProgramSource decls =
  unlines $
    [ "artifact cert_slots_fixture at sha256:cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc"
    , "policy cert-slots-v1"
    , "use backends [ord@1]"
    , ""
    , "claim c_selected"
    , "  nl = \"selected source\""
    , "  formal = selected(sys_a, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "claim c_paired"
    , "  nl = \"paired evidence\""
    , "  formal = paired(sys_a, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "claim c_twinned"
    , "  nl = \"twinned evidence\""
    , "  formal = twinned(sys_a, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "leaf e1 : alpha(sys_a, 0.74)"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = [evidence/alpha.txt]"
    , ""
    , "leaf e2 : beta(sys_a, 0.74)"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = [evidence/beta.txt]"
    , ""
    , "leaf e3 : alpha(sys_b, 0.74)"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = [evidence/other.txt]"
    , ""
    ]
      ++ decls
      ++ [ ""
         , "status c_selected"
         , "status c_paired"
         , "status c_twinned"
         ]

-- | An @assurance = cert(ord\@1, …)@ line over the given payload text.
certLine :: String -> String
certLine payload =
  "  assurance = cert(ord@1, sha256:cert-slots-theory-0, " ++ payload ++ ")"

-- | @pair@ over the two leaf premises, certified by the given payload text.
pairArg :: String -> [String]
pairArg payload =
  [ "arg a_pair : supports(c_paired) by pair(sys_a, 0.74)"
  , certLine payload
  ]

-- | The same instance written in the inferred spelling (@from [e1, e2]@).
pairArgInferred :: String -> [String]
pairArgInferred payload =
  [ "arg a_pair : supports(c_paired) by pair from [e1, e2]"
  , certLine payload
  ]

-- | @twin@ over its one repeated premise pattern, certified by the given
-- payload text. Both slots are filled by @e1@, so a /leaf/ name cannot say
-- which slot it means — this is the instance the @\@0.8@ premise labels exist
-- for (#131).
twinArg :: String -> [String]
twinArg payload =
  [ "arg a_twin : supports(c_twinned) by twin(sys_a, 0.74)"
  , certLine payload
  ]

-- | The repeated-slot fixture with slot 0's label shadowed by a declared leaf.
-- The label exists but cannot repair a reference to @e1@ because citing
-- @left@ is itself ambiguous.
shadowedTwinLabelArg :: String -> [String]
shadowedTwinLabelArg payload =
  [ "leaf left : beta(sys_b, 0.74)"
  , "  kind = observed"
  , "  provenance = user"
  , "  refs = [evidence/shadowed-label.txt]"
  , ""
  ]
    ++ twinArg payload

-- | The pre-@\@0.8@ control: @plain@ is @pair@ with its premise labels
-- removed, so every resolution here runs the path a policy written before
-- #131 takes.
plainArg :: String -> [String]
plainArg payload =
  [ "arg a_plain : supports(c_paired) by plain(sys_a, 0.74)"
  , certLine payload
  ]

-- | The pre-@\@0.8@ multi-slot control: one leaf fills both premises of an
-- unlabelled rule, so its repair must not advertise a label that does not
-- exist.
plainTwinArg :: String -> [String]
plainTwinArg payload =
  [ "arg a_plain_twin : supports(c_twinned) by plainTwin(sys_a, 0.74)"
  , certLine payload
  ]

-- | A partial-label regression fixture: @e1@ fills the two unlabelled
-- @alpha@ slots, while the unrelated @beta@ slot alone has a label. The
-- label therefore cannot repair the ambiguity in @(prem e1)@.
partialTwinArg :: String -> [String]
partialTwinArg payload =
  [ "arg a_partial_twin : supports(c_twinned) by partialTwin(sys_a, 0.74)"
  , certLine payload
  ]

-- | Three matching slots whose first two displayed witnesses are labelled
-- but whose third match is not. This makes checking only the rendered
-- witnesses observably wrong.
partialTripleArg :: String -> [String]
partialTripleArg payload =
  [ "arg a_partial_triple : supports(c_twinned) by partialTriple(sys_a, 0.74)"
  , certLine payload
  ]

-- | A @pair@ instance under a declared leaf whose name is also one of @pair@'s
-- premise labels. Both classes would resolve — and to the same slot — but the
-- collision is rejected outright (@\@0.8@ decision 2, the one collision policy
-- of @\@0.6@\/@\@0.7@).
labelCollisionDecls :: [String]
labelCollisionDecls =
  [ "leaf base : beta(sys_b, 0.74)"
  , "  kind = observed"
  , "  provenance = user"
  , "  refs = [evidence/label-collision.txt]"
  , ""
  ]
    ++ pairArg "(ordcmp (prem base) (prem 1))"

-- | The same cross-class collision as 'labelCollisionDecls', in the /other/
-- class it can happen in: a prior __argument__ whose id is one of the citing
-- rule's premise labels. @promote@ labels its slots @chosen@\/@other@, and the
-- argument it cites in slot 0 is named @chosen@ here.
--
-- The two fixtures reach the resolver's @('Just' _, _)@ catch-all through
-- different 'refMatches' shapes — @([leaf], [])@ there, @([], [prior])@ here —
-- so only both together pin what the guard claims: a label collision with
-- /either/ other class is rejected, never silently resolved to the label's
-- slot.
priorArgLabelCollisionDecls :: [String]
priorArgLabelCollisionDecls =
  [ "arg chosen : supports(c_selected) by select(sys_a, 0.74)"
  , "  assurance = trusted"
  , ""
  , "arg a2 : supports(c_paired) by promote(sys_a, 0.74)"
  , certLine "(ordcmp (prem chosen) (prem 1))"
  ]

-- | @promote@ citing the prior argument @a1@ in premise slot 0 and the leaf
-- @e2@ in slot 1, in the explicit spelling.
priorArg :: String -> [String]
priorArg payload =
  [ "arg a1 : supports(c_selected) by select(sys_a, 0.74)"
  , "  assurance = trusted"
  , ""
  , "arg a2 : supports(c_paired) by promote(sys_a, 0.74)"
  , certLine payload
  ]

-- | The same prior-argument citation in the inferred spelling.
priorArgInferred :: String -> [String]
priorArgInferred payload =
  [ "arg a1 : supports(c_selected) by select(sys_a, 0.74)"
  , "  assurance = trusted"
  , ""
  , "arg a2 : supports(c_paired) by promote from [a1, e2]"
  , certLine payload
  ]

-- ---------------------------------------------------------------------------
-- Elaboration helpers
-- ---------------------------------------------------------------------------

elaborateDecls :: [String] -> Either String (Either ElabError Unit)
elaborateDecls decls = do
  program <- either (Left . show) Right (parseProgram (certProgramSource decls))
  policy <- either (Left . show) Right (parsePolicy certPolicySource)
  pure (elaborate (registryOf policy) program policy)

-- | The elaborated 'Unit' for a fixture that must elaborate.
unitOf :: [String] -> Either String Unit
unitOf decls = case elaborateDecls decls of
  Left err -> Left ("fixture parse failed: " ++ err)
  Right (Left err) -> Left ("unexpected elaboration failure: " ++ elabErrorMessage err)
  Right (Right unit) -> Right unit

-- | Two fixtures elaborate to the very same 'Unit' — the twin property that
-- makes a named slot a pure presentation convenience: nothing downstream can
-- tell which spelling the author used.
sameUnit :: String -> [String] -> [String] -> Property
sameUnit what symbolic numeric =
  case (unitOf symbolic, unitOf numeric) of
    (Left err, _) -> counterexample (what ++ ": " ++ err) False
    (_, Left err) -> counterexample (what ++ " (twin): " ++ err) False
    (Right a, Right b) -> counterexample what (a === b)

-- | A fixture must fail elaboration with the named constructor, and its
-- rendering must carry the given fragments.
expectCertError :: [String] -> (ElabError -> Bool) -> [String] -> Property
expectCertError decls matches fragments =
  case elaborateDecls decls of
    Left err -> counterexample ("fixture parse failed: " ++ err) False
    Right (Right unit) ->
      counterexample ("expected a certificate slot error, got " ++ show unit) False
    Right (Left err) ->
      conjoin
        [ counterexample ("unexpected constructor: " ++ show err) (matches err)
        , counterexample ("message: " ++ elabErrorMessage err) $
            all (`isInfixOf` elabErrorMessage err) fragments
        ]

-- | The exact author-facing diagnostic for a fixture that must fail during
-- certificate-slot elaboration.
certErrorMessage :: [String] -> Either String String
certErrorMessage decls = case elaborateDecls decls of
  Left err -> Left ("fixture parse failed: " ++ err)
  Right (Right unit) -> Left ("expected a certificate slot error, got " ++ show unit)
  Right (Left err) -> Right (elabErrorMessage err)

-- | The certificate payload carried by a support term's assurance.
payloadOf :: SupportTerm -> Maybe SExpr
payloadOf (SRule _ _ _ _ _ (AssuranceCert cert)) = Just (certPayload cert)
payloadOf _ = Nothing

-- ---------------------------------------------------------------------------
-- Elaboration: the symbolic/numeric twin property
-- ---------------------------------------------------------------------------

-- | The headline property (#105): an argument whose certificate cites its
-- premises by source name elaborates to exactly the 'Unit' the numeric
-- spelling produces — same θ, same premises, same payload bytes.
prop_symbolicTwinMatchesNumeric :: Property
prop_symbolicTwinMatchesNumeric = once $
  sameUnit
    "explicit spelling, leaf premises"
    (pairArg "(ordcmp (prem e1) (prem e2))")
    (pairArg "(ordcmp (prem 0) (prem 1))")

-- | The inferred spelling lowers identically: @by pair from [e1, e2]@ with a
-- symbolic certificate is the same 'Unit' as the explicit spelling with a
-- numeric one, so the pass is wired at both elaboration sites.
prop_inferredSpellingLowersIdentically :: Property
prop_inferredSpellingLowersIdentically = once $
  sameUnit
    "inferred spelling, leaf premises"
    (pairArgInferred "(ordcmp (prem e1) (prem e2))")
    (pairArg "(ordcmp (prem 0) (prem 1))")

-- | A mixed payload is lowered position-wise: the symbolic reference moves,
-- the numeric one is left alone.
prop_mixedSpellingLowers :: Property
prop_mixedSpellingLowers = once $
  sameUnit
    "mixed symbolic/numeric positions"
    (pairArg "(ordcmp (prem e1) (prem 1))")
    (pairArg "(ordcmp (prem 0) (prem 1))")

-- | D4's representation rule: a citation of a /prior argument/ resolves the
-- same way in both spellings. Both fixtures below name @a1@ in premise slot 0,
-- and both must agree with the numeric twin — a name must never lower under
-- @from […]@ and fail under the explicit spelling.
prop_priorArgumentCitationBothSpellings :: Property
prop_priorArgumentCitationBothSpellings = once $
  conjoin
    [ sameUnit
        "prior argument, explicit spelling"
        (priorArg "(ordcmp (prem a1) (prem e2))")
        (priorArg "(ordcmp (prem 0) (prem 1))")
    , sameUnit
        "prior argument, inferred spelling"
        (priorArgInferred "(ordcmp (prem a1) (prem e2))")
        (priorArg "(ordcmp (prem 0) (prem 1))")
    ]

-- ---------------------------------------------------------------------------
-- Elaboration: premise-label citation (lara-syntax@0.8, #131)
-- ---------------------------------------------------------------------------

-- | #131's twin property: a certificate citing its rule's declared premise
-- __labels__ elaborates to exactly the 'Unit' the numeric spelling produces.
-- Pinned at both elaboration sites, because a label resolves the same way
-- under @from […]@ as it does under an explicit θ.
prop_labelCitationLowersToNumericTwin :: Property
prop_labelCitationLowersToNumericTwin = once $
  conjoin
    [ sameUnit
        "premise-label citation, explicit spelling"
        (pairArg "(ordcmp (prem base) (prem new))")
        (pairArg "(ordcmp (prem 0) (prem 1))")
    , sameUnit
        "premise-label citation, inferred spelling"
        (pairArgInferred "(ordcmp (prem base) (prem new))")
        (pairArg "(ordcmp (prem 0) (prem 1))")
    , sameUnit
        "labels and numerals mix position-wise"
        (pairArg "(ordcmp (prem base) (prem 1))")
        (pairArg "(ordcmp (prem 0) (prem 1))")
    ]

-- | #131's headline: labels name the /slots/, so they keep working in the one
-- case the @\@0.6@ leaf\/prior namespace cannot express. @twin@'s two premises
-- share one pattern, so the leaf @e1@ fills both and its name is
-- 'CertSlotMultiSlot' — while @left@ and @right@ resolve, because a label
-- names a slot rather than the term that fills it. Both halves are asserted
-- together: the contrast /is/ the feature.
prop_labelResolvesMultiSlot :: Property
prop_labelResolvesMultiSlot = once $
  conjoin
    [ sameUnit
        "labels cite the two slots one leaf fills"
        (twinArg "(ordcmp (prem left) (prem right))")
        (twinArg "(ordcmp (prem 0) (prem 1))")
    , expectCertError
        (twinArg "(ordcmp (prem e1) (prem 1))")
        ( \err -> case err of
            CertSlotMultiSlot (ArgId "a_twin") (AST.BackendId "ord") 1 (AST.ArgRef "e1") 0 1 True -> True
            _ -> False
        )
        [ "arg 'a_twin'"
        , "'e1'"
        , "occupies premise slots 0 and 1"
        , "cite a numeric slot or the rule's premise label for the slot you mean"
        ]
    ]

-- | #140: label advice is valid only when every slot matched by the
-- ambiguous source name has its own label. An unrelated labelled slot must
-- not turn a numeric-only repair into the two-exit repair wording.
prop_partialLabelsDoNotAdvertiseUnavailableRepair :: Property
prop_partialLabelsDoNotAdvertiseUnavailableRepair = once $
  counterexample "an unrelated premise label enabled impossible label repair advice" $
    certErrorMessage (partialTwinArg "(ordcmp (prem e1) (prem 1))")
      === Right "arg 'a_partial_twin': certificate 'ord@1' premise reference 'e1' occupies premise slots 0 and 1; cite a numeric slot"

-- | The availability condition is computed from the complete matching-slot
-- set, not merely the two witnesses retained for the diagnostic.
prop_allMatchingSlotsNeedLabels :: Property
prop_allMatchingSlotsNeedLabels = once $
  counterexample "only the first two of three matching slots were checked for labels" $
    certErrorMessage (partialTripleArg "(ordcmp (prem e1) (prem 1))")
      === Right "arg 'a_partial_triple': certificate 'ord@1' premise reference 'e1' occupies premise slots 0 and 1; cite a numeric slot"

-- | #140: every matching slot needs a label that the same resolver would
-- accept. Merely declaring @left@ does not make it actionable when a leaf
-- shadows that label.
prop_shadowedLabelDoesNotAdvertiseUnavailableRepair :: Property
prop_shadowedLabelDoesNotAdvertiseUnavailableRepair = once $
  conjoin
    [ expectCertError
        (shadowedTwinLabelArg "(ordcmp (prem e1) (prem 1))")
        ( \err -> case err of
            CertSlotMultiSlot (ArgId "a_twin") (AST.BackendId "ord") 1 (AST.ArgRef "e1") 0 1 False -> True
            _ -> False
        )
        [ "arg 'a_twin'"
        , "'e1'"
        , "occupies premise slots 0 and 1"
        , "cite a numeric slot"
        ]
    , expectCertError
        (shadowedTwinLabelArg "(ordcmp (prem left) (prem 1))")
        ( \err -> case err of
            CertSlotLabelAmbiguous (ArgId "a_twin") (AST.BackendId "ord") 1 (AST.ArgRef "left") (RuleId "twin") -> True
            _ -> False
        )
        [ "arg 'a_twin'"
        , "'left'"
        , "is ambiguous between rule 'twin' premise label and a declared leaf or prior argument"
        ]
    ]

-- | Decision 2: a name carried by /both/ a premise label and a declared leaf
-- is a hard error — even here, where both classes would resolve to the same
-- slot. Predictability over convenience: an agreeing-referent carve-out would
-- be the first conditional rule in an otherwise uniform collision policy.
prop_labelLeafCollisionIsHardError :: Property
prop_labelLeafCollisionIsHardError = once $
  expectCertError
    labelCollisionDecls
    ( \err -> case err of
        CertSlotLabelAmbiguous (ArgId "a_pair") (AST.BackendId "ord") 1 (AST.ArgRef "base") (RuleId "pair") -> True
        _ -> False
    )
    [ "arg 'a_pair'"
    , "'base'"
    , "is ambiguous between rule 'pair' premise label and a declared leaf or prior argument"
    ]

-- | Decision 2's other half: the colliding name is carried by a premise label
-- and a prior __argument__ rather than a declared leaf. Same verdict, same
-- reason — and it is the half a narrowing refactor would drop, because the
-- resolver's @('Just' _, _)@ pattern covers all three 'refMatches' shapes at
-- once while 'labelLeafCollisionIsHardError' only observes @([leaf], [])@.
prop_labelPriorArgumentCollisionIsHardError :: Property
prop_labelPriorArgumentCollisionIsHardError = once $
  expectCertError
    priorArgLabelCollisionDecls
    ( \err -> case err of
        CertSlotLabelAmbiguous (ArgId "a2") (AST.BackendId "ord") 1 (AST.ArgRef "chosen") (RuleId "promote") -> True
        _ -> False
    )
    [ "arg 'a2'"
    , "'chosen'"
    , "is ambiguous between rule 'promote' premise label and a declared leaf or prior argument"
    ]

-- | The one guard the label class carries, pinned. A label names a /slot/, so
-- it resolves against the rule's declared premise list — but the slot it names
-- must exist in __this instance's__ premise list, and an authored premise list
-- shorter than the rule's can violate that. @promote@ labels two slots; this
-- instance is written out with one premise, so @other@ (slot 1) names a slot
-- that is not there.
--
-- Reachable only from an authored premise list: 'elabTerm''s explicit-premise
-- path elaborates its premises verbatim with no arity check against the rule's
-- declared list, unlike the inferred path. Without this pin, dropping the
-- guard (or inverting it to @i <= length prems@) would lower @(prem other)@ to
-- an out-of-range @(prem 1)@ and the suite would stay green — the suite's only
-- other 'CertSlotNotAPremise' fixture cites a /leaf/ and reaches the verdict
-- through 'locate''s @[]@ case, a different path.
--
-- The verdict reuses 'CertSlotNotAPremise', whose template reads \"does not
-- resolve to any of this argument's premise slots\". Read strictly that is a
-- statement about the slot, not the name: @other@ /did/ resolve, to a slot
-- this instance lacks. The wording is kept rather than split into an eighth
-- family because the @\@0.8@ family list is frozen (grammar App. G.5) and both
-- cases are the same author mistake — citing a premise this instance does not
-- have.
prop_labelSlotOutsideAuthoredPremises :: Property
prop_labelSlotOutsideAuthoredPremises = once $
  case elaborateRewrittenA2 shortPremiseList of
    Right term -> counterexample ("expected rejection, got " ++ show term) False
    Left msg ->
      property $
        "arg 'a2'" `isInfixOf` msg
          && "'other'" `isInfixOf` msg
          && "does not resolve to any of this argument's premise slots" `isInfixOf` msg
  where
    shortPremiseList a1Term =
      withPremisesAndCert
        [a1Term]
        (ordAssurance (ordcmp (prem "other") (prem "0")))

-- | The unresolved verdict now names the rule and all three classes, so an
-- author who mistyped a label is told a label was one of the things looked for.
prop_unresolvedNamesAllThreeClasses :: Property
prop_unresolvedNamesAllThreeClasses = once $
  expectCertError
    (pairArg "(ordcmp (prem no_such) (prem 1))")
    ( \err -> case err of
        CertSlotUnresolved (ArgId "a_pair") (AST.BackendId "ord") 1 (AST.ArgRef "no_such") (RuleId "pair") -> True
        _ -> False
    )
    [ "arg 'a_pair'"
    , "'no_such'"
    , "names neither a premise label of rule 'pair', a declared leaf, nor a prior argument"
    ]

-- | Conservativity for every policy written before @\@0.8@ — which is every
-- policy in the frozen corpus. A rule with no premise labels leaves
-- 'premiseLabelIndex' returning 'Nothing' for /every/ name, so the third class
-- is not merely unused but unreachable, and both the resolving and the failing
-- path must read exactly as they did at @\@0.6@. Pinned on both, because the
-- resolver's case split changed shape around them.
prop_unlabelledRuleResolvesAsBefore :: Property
prop_unlabelledRuleResolvesAsBefore = once $
  conjoin
    [ sameUnit
        "unlabelled rule, leaf citation"
        (plainArg "(ordcmp (prem e1) (prem e2))")
        (plainArg "(ordcmp (prem 0) (prem 1))")
    , expectCertError
        (plainArg "(ordcmp (prem e9) (prem 1))")
        ( \err -> case err of
            CertSlotUnresolved (ArgId "a_plain") (AST.BackendId "ord") 1 (AST.ArgRef "e9") (RuleId "plain") -> True
            _ -> False
        )
        ["arg 'a_plain'", "'e9'", "premise label of rule 'plain'"]
    , -- A label of a labelled rule is not a name an unlabelled rule knows:
      -- the class is per-rule, not per-policy.
      expectCertError
        (plainArg "(ordcmp (prem base) (prem 1))")
        ( \err -> case err of
            CertSlotUnresolved (ArgId "a_plain") (AST.BackendId "ord") 1 (AST.ArgRef "base") (RuleId "plain") -> True
            _ -> False
        )
        ["arg 'a_plain'", "'base'"]
    ]

-- ---------------------------------------------------------------------------
-- Elaboration: the seven author-facing failures
-- ---------------------------------------------------------------------------

prop_certSlotFailureMatrix :: Property
prop_certSlotFailureMatrix =
  conjoin
    [ once $
        expectCertError
          (pairArg "(ordcmp (prem e9) (prem e2))")
          ( \err -> case err of
              CertSlotUnresolved (ArgId "a_pair") (AST.BackendId "ord") 1 (AST.ArgRef "e9") (RuleId "pair") -> True
              _ -> False
          )
          [ "arg 'a_pair'"
          , "'ord@1'"
          , "'e9'"
          , "names neither a premise label of rule 'pair', a declared leaf, nor a prior argument"
          ]
    , once $
        expectCertError
          labelCollisionDecls
          ( \err -> case err of
              CertSlotLabelAmbiguous (ArgId "a_pair") (AST.BackendId "ord") 1 (AST.ArgRef "base") (RuleId "pair") -> True
              _ -> False
          )
          ["arg 'a_pair'", "'base'", "is ambiguous between rule 'pair' premise label"]
    , once $
        expectCertError
          ambiguousDecls
          ( \err -> case err of
              CertSlotAmbiguous (ArgId "a_bad") (AST.BackendId "ord") 1 (AST.ArgRef "a1") -> True
              _ -> False
          )
          ["arg 'a_bad'", "'a1'", "ambiguous between a declared leaf and a prior argument"]
    , once $
        expectCertError
          (pairArg "(ordcmp (prem e3) (prem e2))")
          ( \err -> case err of
              CertSlotNotAPremise (ArgId "a_pair") (AST.BackendId "ord") 1 (AST.ArgRef "e3") -> True
              _ -> False
          )
          ["arg 'a_pair'", "'e3'", "does not resolve to any of this argument's premise slots"]
    , once $
        expectCertError
          (twinArg "(ordcmp (prem e1) (prem 1))")
          ( \err -> case err of
              CertSlotMultiSlot (ArgId "a_twin") (AST.BackendId "ord") 1 (AST.ArgRef "e1") 0 1 True -> True
              _ -> False
          )
          [ "arg 'a_twin'"
          , "'e1'"
          , "occupies premise slots 0 and 1"
          , "cite a numeric slot or the rule's premise label for the slot you mean"
          ]
    , once $
        expectCertError
          (plainTwinArg "(ordcmp (prem e1) (prem 1))")
          ( \err -> case err of
              CertSlotMultiSlot (ArgId "a_plain_twin") (AST.BackendId "ord") 1 (AST.ArgRef "e1") 0 1 False -> True
              _ -> False
          )
          [ "arg 'a_plain_twin'"
          , "'e1'"
          , "occupies premise slots 0 and 1"
          , "cite a numeric slot"
          ]
    , once $
        expectCertError
          (pairArg "(ordcmp (prem 007) (prem 1))")
          ( \err -> case err of
              CertSlotNonCanonicalNumeral (ArgId "a_pair") (AST.BackendId "ord") 1 (AST.ArgRef "007") -> True
              _ -> False
          )
          ["arg 'a_pair'", "'007'", "not a canonical slot numeral"]
    , once $
        expectCertError
          (pairArg "(ordcmp (prem e1))")
          ( \err -> case err of
              CertSlotSchemaMismatch (ArgId "a_pair") (AST.BackendId "ord") 1 (AST.ArgRef "e1") -> True
              _ -> False
          )
          ["arg 'a_pair'", "does not match the backend's premise-reference schema", "'e1'"]
    ]
  where
    -- @a1@ names both a declared leaf and a prior argument, so the citation is
    -- ambiguous — the same collision 'resolveArgRef' rejects for a θ reference.
    ambiguousDecls =
      [ "leaf a1 : beta(sys_b, 0.74)"
      , "  kind = observed"
      , "  provenance = user"
      , "  refs = [evidence/collision.txt]"
      , ""
      , "arg a1 : supports(c_selected) by select(sys_a, 0.74)"
      , "  assurance = trusted"
      , ""
      , "arg a_bad : supports(c_paired) by pair(sys_a, 0.74)"
      , certLine "(ordcmp (prem a1) (prem e2))"
      ]

-- | The @InferTheta@ site enforces the failures too, not just the successes:
-- the same undeclared name under @from […]@ is rejected with the same
-- constructor and rendering.
prop_inferredSpellingRejectsUnresolved :: Property
prop_inferredSpellingRejectsUnresolved = once $
  expectCertError
    (pairArgInferred "(ordcmp (prem e9) (prem e2))")
    ( \err -> case err of
        CertSlotUnresolved (ArgId "a_pair") (AST.BackendId "ord") 1 (AST.ArgRef "e9") (RuleId "pair") -> True
        _ -> False
    )
    [ "arg 'a_pair'"
    , "'e9'"
    , "names neither a premise label of rule 'pair', a declared leaf, nor a prior argument"
    ]

-- | A marker-free @nd\@1@ payload is untouched by named proof-term lowering;
-- malformed kernel payloads remain the strict decoder's concern.
prop_schemalessBackendUntouched :: Property
prop_schemalessBackendUntouched = once $
  case unitOf decls of
    Left err -> counterexample err False
    Right unit ->
      counterexample (show (lookup (ArgId "a_nd") (unitArgs unit))) $
        (payloadOf =<< lookup (ArgId "a_nd") (unitArgs unit))
          === Just (SList [SAtom "app", SList [SAtom "hyp", SAtom "0"]])
  where
    decls =
      [ "arg a_nd : supports(c_paired) by pair(sys_a, 0.74)"
      , "  assurance = cert(nd@1, sha256:cert-slots-theory-0, (app (hyp 0)))"
      ]

-- ---------------------------------------------------------------------------
-- Elaboration: recursion into nested rule instances (D8)
-- ---------------------------------------------------------------------------
--
-- Reachability note: @lara-syntax\@0.6@'s surface grammar cannot author a
-- nested certificate. 'Lara.Syntax.explicitRuleP' always sets @srPremises = []@
-- and 'Lara.Syntax.assuranceP' only ever attaches to the @arg@ block's own rule
-- application, so every /parsed/ premise list is reconstructed by
-- @resolvePremises@ and carries whatever assurance its own @arg@ declared.
-- The recursive lowering is therefore reachable only from a hand-built AST
-- today — but it is on the path the moment premises become authorable, so the
-- two fixtures below pin it through the real elaborator entry point.

-- | Replace one argument's instantiation in a parsed program.
replaceArgInstantiation :: ArgId -> (ArgInstantiation -> ArgInstantiation) -> Program -> Program
replaceArgInstantiation target f program =
  program
    { programDecls =
        [ case decl of
            DeclArg arg | argId arg == target -> DeclArg arg {argInstantiation = f (argInstantiation arg)}
            _ -> decl
        | decl <- programDecls program
        ]
    }

-- | The surface support term a parsed argument carries, for reuse as a nested
-- premise (so the fixture never hand-builds a θ term).
surfaceTermOf :: Program -> ArgId -> Maybe SupportTerm
surfaceTermOf program target =
  case [argInstantiation a | DeclArg a <- programDecls program, argId a == target] of
    [ExplicitTheta t] -> Just t
    _ -> Nothing

-- | An @ord\@1@ certificate over the given payload, as the elaborator holds it
-- before lowering.
ordAssurance :: SExpr -> Assurance
ordAssurance payload =
  AssuranceCert
    Cert
      { certBackend = AST.BackendId "ord"
      , certVersion = 1
      , certTheory = TheoryDigest "sha256:cert-slots-theory-0"
      , certPayload = payload
      }

-- | Give a parsed rule instance an authored premise list and assurance — the
-- two things the @\@0.6@ surface grammar cannot write.
withPremisesAndCert :: [SupportTerm] -> Assurance -> SupportTerm -> SupportTerm
withPremisesAndCert prems assurance (SRule r th _ ds hs _) = SRule r th prems ds hs assurance
withPremisesAndCert _ _ term = term

-- | Elaborate the two-argument fixture below after rewriting @a2@'s support
-- term by hand, and return @a2@'s /elaborated/ term. The rewrite receives
-- @a1@'s and @a2@'s parsed surface terms, so no fixture hand-builds a θ.
elaborateRewrittenA2 :: (SupportTerm -> SupportTerm -> SupportTerm) -> Either String SupportTerm
elaborateRewrittenA2 rewrite = do
  program <- either (Left . show) Right (parseProgram source)
  policy <- either (Left . show) Right (parsePolicy certPolicySource)
  a1Term <- maybe (Left "fixture lost arg a1") Right (surfaceTermOf program (ArgId "a1"))
  a2Term <- maybe (Left "fixture lost arg a2") Right (surfaceTermOf program (ArgId "a2"))
  let rewritten =
        replaceArgInstantiation
          (ArgId "a2")
          (const (ExplicitTheta (rewrite a1Term a2Term)))
          program
  unit <- either (Left . elabErrorMessage) Right (elaborate (registryOf policy) rewritten policy)
  maybe (Left "arg a2 vanished from the Unit") Right (lookup (ArgId "a2") (unitArgs unit))
  where
    source =
      certProgramSource
        [ "arg a1 : supports(c_selected) by select(sys_a, 0.74)"
        , "  assurance = trusted"
        , ""
        , "arg a2 : supports(c_paired) by promote(sys_a, 0.74)"
        , "  assurance = trusted"
        ]

-- | D8: a certificate on a /nested/ instance lowers against that instance's
-- own premise list, not the enclosing one. The nested @select@ has a single
-- premise (@e1@ at slot 0), so its @(prem e1)@ becomes @(prem 0)@ while the
-- enclosing @promote@ — whose slot 0 is that very @select@ — is untouched.
prop_lowersNestedCertificate :: Property
prop_lowersNestedCertificate = once $
  case elaborateRewrittenA2 (nestedCert (ordcmp (prem "e1") (prem "0"))) of
    Left err -> counterexample err False
    Right (SRule _ _ [inner, SLeaf (LeafId "e2")] _ _ AssuranceTrusted) ->
      payloadOf inner === Just (ordcmp (prem "0") (prem "0"))
    Right other -> counterexample ("unexpected a2 term: " ++ show other) False

-- | The @\@0.8@ half of D8 (#131): premise __labels__ are scoped to the rule
-- of the instance that cites them, exactly as the leaf\/prior classes are
-- scoped to that instance's premise list.
--
-- The nesting is @promote@ (labels @chosen@\/@other@) over a nested @select@
-- (label @src@). Inside the nested certificate, @src@ resolves — against
-- @select@'s own single premise — and @chosen@, a label of the /enclosing/
-- rule, does not resolve at all. A leaked label would be the worst kind of
-- silent success: it names a slot index that exists in both instances.
prop_nestedCertificateLabelScope :: Property
prop_nestedCertificateLabelScope = once $
  conjoin
    [ counterexample "the nested rule's own label lowers against its own premises" $
        case elaborateRewrittenA2 (nestedCert (ordcmp (prem "src") (prem "0"))) of
          Left err -> counterexample err False
          Right (SRule _ _ [inner, _] _ _ _) ->
            payloadOf inner === Just (ordcmp (prem "0") (prem "0"))
          Right other -> counterexample ("unexpected a2 term: " ++ show other) False
    , counterexample "a label of the enclosing rule is unresolved in the nested certificate" $
        case elaborateRewrittenA2 (nestedCert (ordcmp (prem "chosen") (prem "0"))) of
          Right term -> counterexample ("expected rejection, got " ++ show term) False
          Left msg ->
            property $
              "premise label of rule 'select'" `isInfixOf` msg
                && "'chosen'" `isInfixOf` msg
    ]

-- | @a2@ rewritten so its premise slot 0 is the nested @select@ instance
-- carrying the given certificate payload, and slot 1 is the leaf @e2@. The
-- trailing @a2Term@ argument 'elaborateRewrittenA2' supplies is the term
-- 'withPremisesAndCert' rewrites, so it stays implicit.
nestedCert :: SExpr -> SupportTerm -> SupportTerm -> SupportTerm
nestedCert payload a1Term =
  withPremisesAndCert
    [ withPremisesAndCert [] (ordAssurance payload) a1Term
    , SLeaf (LeafId "e2")
    ]
    AssuranceTrusted

-- | The representation rule, pinned at the one place the two spellings could
-- diverge. An authored premise list spells a prior argument the way the parser
-- spells every identifier — @'SLeaf' ('LeafId' "a1")@ — while
-- @resolvePremises@ stores that argument's /elaborated term/. The resolver
-- accepts both, so @(prem a1)@ never lowers under @from […]@ and then fails
-- with a spurious "not a premise" once the same instance is written out.
prop_priorArgumentPremiseSpellingsAgree :: Property
prop_priorArgumentPremiseSpellingsAgree = once $
  case elaborateRewrittenA2 (\_ a2Term -> spelledOut a2Term) of
    Left err -> counterexample err False
    Right term@(SRule _ _ prems _ _ _) ->
      conjoin
        [ counterexample ("premises rewritten: " ++ show prems) (prems === spelledOutPremises)
        , counterexample ("payload: " ++ show (payloadOf term)) $
            payloadOf term === Just (ordcmp (prem "0") (prem "1"))
        ]
    Right other -> counterexample ("unexpected a2 term: " ++ show other) False
  where
    spelledOut =
      withPremisesAndCert
        spelledOutPremises
        (ordAssurance (ordcmp (prem "a1") (prem "e2")))
    spelledOutPremises = [SLeaf (LeafId "a1"), SLeaf (LeafId "e2")]

-- ---------------------------------------------------------------------------
-- End-to-end fixtures: parse + elaborate + encode + check + replay
-- ---------------------------------------------------------------------------
--
-- A second, checking-capable fixture family. The @cert-slots-v1@ rules above
-- conclude domain atoms no backend certifies, so their certificates can never
-- replay-accept; these rules conclude the exact goal shapes the registered
-- backends decide — @num_lt@ for @ord\@1@ ("Lara.Strict.Ord", the S2 shape),
-- @rel_drop_ge@ for @ra\@1@ ("Lara.Strict.RA", the corpus C04 numbers, so the
-- witness fraction is the plan's @frac 119 500@), and premise-≡-conclusion
-- citation for @nd\@1@ (the S1 shape). One program carries the ord cells on
-- leaves @e1@\/@e2@ and the ra cells on @eA@\/@eB@; each fixture splices in
-- one argument.

e2ePolicySource :: String
e2ePolicySource =
  unlines
    [ "policy cert-slots-e2e-v1"
    , "sort Experiment, Cell"
    , "con exp1 : Experiment"
    , "con cell_a(Num) : Cell"
    , "con cell_b(Num) : Cell"
    , "pred reports(Experiment, Cell)"
    , "pred num_lt(Num, Num)"
    , "pred rel_drop_ge(Num, Num, Num, Num)"
    , "rule lt_recheck(Exp, Av, Bv)"
    , "  mode = strict"
    , "  premises = [ reports(Exp, cell_a(Av)), reports(Exp, cell_b(Bv)) ]"
    , "  conclusion = num_lt(Av, Bv)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ord@1, sha256:cert-slots-theory-0) ]"
    , "rule drop_recheck(Exp, F, A, R, T)"
    , "  mode = strict"
    , "  premises = [ reports(Exp, cell_a(F)), reports(Exp, cell_b(A)) ]"
    , "  conclusion = rel_drop_ge(F, A, R, T)"
    , "  allow-trusted = false"
    , "  certifiers = [ (ra@1, sha256:corpus-v1-ra-theory-0) ]"
    , "rule cite(Exp, V)"
    , "  mode = strict"
    , "  premises = [ reports(Exp, cell_a(V)) ]"
    , "  conclusion = reports(Exp, cell_a(V))"
    , "  allow-trusted = false"
    , "  certifiers = [ (nd@1, sha256:cert-slots-nd-theory-0) ]"
    , "theory sha256:cert-slots-theory-0 = []"
    , "theory sha256:corpus-v1-ra-theory-0 = []"
    , "theory sha256:cert-slots-nd-theory-0 = []"
    ]

e2eProgramSource :: [String] -> String
e2eProgramSource decls =
  unlines $
    [ "artifact cert_slots_e2e at sha256:" ++ replicate 64 'd'
    , "policy cert-slots-e2e-v1"
    , "use backends [nd@1, ord@1, ra@1]"
    , ""
    , "claim c_lt"
    , "  nl = \"the base cell is strictly below the new cell\""
    , "  formal = num_lt(0.71, 0.74)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "claim c_drop"
    , "  nl = \"the ablation drop clears the threshold\""
    , "  formal = rel_drop_ge(50, 38.1, 0.238, 0.05)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "claim c_cite"
    , "  nl = \"the base cell is reported\""
    , "  formal = reports(exp1, cell_a(0.71))"
    , "  binding = { author = alice, audit-status = reviewed }"
    , ""
    , "leaf e1 : reports(exp1, cell_a(0.71))"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = [evidence/cells.md#base]"
    , ""
    , "leaf e2 : reports(exp1, cell_b(0.74))"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = [evidence/cells.md#new]"
    , ""
    , "leaf eA : reports(exp1, cell_a(50))"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = [evidence/cells.md#full]"
    , ""
    , "leaf eB : reports(exp1, cell_b(38.1))"
    , "  kind = observed"
    , "  provenance = user"
    , "  refs = [evidence/cells.md#ablated]"
    , ""
    ]
      ++ decls
      ++ [ ""
         , "status c_lt"
         , "status c_drop"
         , "status c_cite"
         ]

-- | The @ord\@1@ comparison argument over leaves @e1@\/@e2@.
ordE2EArg :: String -> [String]
ordE2EArg payload =
  [ "arg a_lt : supports(c_lt) by lt_recheck(exp1, 0.71, 0.74)"
  , "  assurance = cert(ord@1, sha256:cert-slots-theory-0, " ++ payload ++ ")"
  ]

-- | The @ra\@1@ relative-drop argument over leaves @eA@\/@eB@.
raE2EArg :: String -> [String]
raE2EArg payload =
  [ "arg a_drop : supports(c_drop) by drop_recheck(exp1, 50, 38.1, 0.238, 0.05)"
  , "  assurance = cert(ra@1, sha256:corpus-v1-ra-theory-0, " ++ payload ++ ")"
  ]

-- | The @nd\@1@ citation argument over leaf @e1@ (the S1 hypothesis-reuse shape).
ndE2EArg :: String -> [String]
ndE2EArg payload =
  [ "arg a_cite : supports(c_cite) by cite(exp1, 0.71)"
  , "  assurance = cert(nd@1, sha256:cert-slots-nd-theory-0, " ++ payload ++ ")"
  ]

-- | Parse and elaborate one end-to-end fixture, keeping the parsed pair for
-- the replay-identity construction.
e2eElaborated :: [String] -> Either String (Program, Policy, Unit)
e2eElaborated decls = do
  program <- either (Left . show) Right (parseProgram (e2eProgramSource decls))
  policy <- either (Left . show) Right (parsePolicy e2ePolicySource)
  unit <- either (Left . elabErrorMessage) Right (elaborate (registryOf policy) program policy)
  pure (program, policy, unit)

-- | The full production pipeline the worked-example goldens pin
-- ('Lara.Elaborate.prepareSource' + 'runSourceCheck'), down to the 'Verdict'.
e2eVerdict :: [String] -> Either String Verdict
e2eVerdict decls = do
  (program, policy, _) <- e2eElaborated decls
  case prepareSource program policy of
    Left invalid -> Left ("source invalid: " ++ renderSourceInvalid invalid)
    Right (SourceRejected rejection) ->
      Left ("admission rejection: " ++ renderAdmissionRejection rejection)
    Right (SourceAccepted input) -> Right (sourceResultVerdict (runSourceCheck input))

-- | The replay identity + check input over a (possibly rewritten) unit — the
-- raw-door construction "ReplaySpec"'s @rawInputFor@ uses.
e2eCheckInput :: Program -> Policy -> Unit -> Either ReplayError CheckInput
e2eCheckInput program policy unit = do
  replayId <-
    mkReplayId
      LaraCoreV02
      (policyId policy)
      (programBackends program)
      (sort (map fst (policyTheories policy)))
      (programDigest program)
  mkCheckInput replayId unit

-- ---------------------------------------------------------------------------
-- End-to-end: byte-identity on the wire, both backends
-- ---------------------------------------------------------------------------

-- | Two fixtures encode to the very same wire bytes, and the symbolic twin's
-- bytes carry the given lowered-payload spelling (so equality is not vacuous).
sameWireBytes :: String -> String -> Either String Unit -> Either String Unit -> Property
sameWireBytes what lowered symbolic numeric =
  case (symbolic, numeric) of
    (Left err, _) -> counterexample (what ++ ": " ++ err) False
    (_, Left err) -> counterexample (what ++ " (twin): " ++ err) False
    (Right a, Right b) ->
      let bytesA = printSExpr (encodeUnit a)
          bytesB = printSExpr (encodeUnit b)
       in conjoin
            [ counterexample (what ++ ": encoded bytes differ") (bytesA === bytesB)
            , counterexample
                (what ++ ": lowered payload " ++ lowered ++ " absent from the wire")
                (property (lowered `isInfixOf` bytesA))
            ]

-- | #105's verification target verbatim, @ord\@1@: the Task-3 fixture pair's
-- symbolic and numeric spellings lower to byte-identical Cert payloads and
-- units under the wire encoder.
prop_ordTwinsEncodeByteIdentical :: Property
prop_ordTwinsEncodeByteIdentical = once $
  sameWireBytes
    "ord@1 twins"
    "(ordcmp (prem 0) (prem 1))"
    (unitOf (pairArg "(ordcmp (prem e1) (prem e2))"))
    (unitOf (pairArg "(ordcmp (prem 0) (prem 1))"))

-- | The same target on @ra\@1@, whose witness fraction rides along untouched.
prop_raTwinsEncodeByteIdentical :: Property
prop_raTwinsEncodeByteIdentical = once $
  sameWireBytes
    "ra@1 twins"
    "(radrop (prem 0) (prem 1) (frac 119 500))"
    (unitFor (raE2EArg "(radrop (prem eA) (prem eB) (frac 119 500))"))
    (unitFor (raE2EArg "(radrop (prem 0) (prem 1) (frac 119 500))"))
  where
    unitFor decls = (\(_, _, unit) -> unit) <$> e2eElaborated decls

-- ---------------------------------------------------------------------------
-- End-to-end: verdict identity through the production pipeline
-- ---------------------------------------------------------------------------

-- | Both spellings of one fixture reach byte-identical verdicts, the verdict
-- is an accept with the certified argument @in@, and the fixture's claim is
-- the justified one (its two siblings stay gap) — so the certificate actually
-- replayed rather than the twins agreeing on a rejection.
sameVerdict :: String -> [String] -> [String] -> Int -> Property
sameVerdict what symbolic numeric justifiedIx =
  case (e2eVerdict symbolic, e2eVerdict numeric) of
    (Left err, _) -> counterexample (what ++ ": " ++ err) False
    (_, Left err) -> counterexample (what ++ " (twin): " ++ err) False
    (Right a, Right b) ->
      conjoin
        [ counterexample (what ++ ": verdict bytes differ") $
            printSExpr (encodeVerdict a) === printSExpr (encodeVerdict b)
        , case verdictOutcome a of
            Reject rejection ->
              counterexample (what ++ ": unexpected reject " ++ show rejection) False
            outcome@Accept{} ->
              conjoin
                [ counterexample (what ++ ": certified arg not in") $
                    verdictLabels outcome === [(0, LIn)]
                , counterexample (what ++ ": statuses drifted") $
                    map snd (verdictStatuses outcome)
                      === [ if ix == justifiedIx then Published Justified else Published Gap
                          | ix <- [0 .. 2]
                          ]
                ]
        ]

prop_ordE2EVerdictIdentity :: Property
prop_ordE2EVerdictIdentity = once $
  sameVerdict
    "ord@1 end-to-end"
    (ordE2EArg "(ordcmp (prem e1) (prem e2))")
    (ordE2EArg "(ordcmp (prem 0) (prem 1))")
    0

prop_raE2EVerdictIdentity :: Property
prop_raE2EVerdictIdentity = once $
  sameVerdict
    "ra@1 end-to-end"
    (raE2EArg "(radrop (prem eA) (prem eB) (frac 119 500))")
    (raE2EArg "(radrop (prem 0) (prem 1) (frac 119 500))")
    1

-- ---------------------------------------------------------------------------
-- End-to-end: replay and tamper (the #57 harness, unchanged)
-- ---------------------------------------------------------------------------

-- | Replace every top-level certificate payload in the unit's arguments — the
-- "MutationSpec" @cert-payload-tamper@ rewrite, with a chosen payload.
tamperCertPayloads :: SExpr -> Unit -> Unit
tamperCertPayloads payload unit =
  unit {unitArgs = [(i, swap t) | (i, t) <- unitArgs unit]}
  where
    swap (SRule r th ps ds hs (AssuranceCert cert)) =
      SRule r th ps ds hs (AssuranceCert cert {certPayload = payload})
    swap t = t

-- | One symbolic fixture through the raw replay door: preflight passes, the
-- lowered unit replays to an accept, and the unit with a single tampered
-- payload byte still passes preflight but is rejected R13 at the certificate
-- replay gate — the argument never reaches the accept semantics, exactly the
-- pre-#105 tamper behavior.
replayThenTamper :: String -> [String] -> SExpr -> Property
replayThenTamper what decls tampered =
  case e2eElaborated decls of
    Left err -> counterexample (what ++ ": " ++ err) False
    Right (program, policy, unit) ->
      let withInput stage u k =
            case e2eCheckInput program policy u of
              Left err ->
                counterexample (what ++ " (" ++ stage ++ "): " ++ replayErrorMessage err) False
              Right input -> k input
       in conjoin
            [ withInput "lowered" unit $ \input ->
                conjoin
                  [ counterexample (what ++ ": replay preflight failed") $
                      runtimeReplayFailure input === Nothing
                  , case verdictOutcome (runCheck input) of
                      Reject rejection ->
                        counterexample (what ++ ": lowered unit rejected " ++ show rejection) False
                      Accept{} -> property True
                  ]
            , withInput "tampered" (tamperCertPayloads tampered unit) $ \input ->
                conjoin
                  [ counterexample (what ++ ": tampering must not trip preflight") $
                      runtimeReplayFailure input === Nothing
                  , counterexample (what ++ ": tampered payload must reject R13") $
                      verdictOutcome (runCheck input) === Reject (RejectClass R13)
                  ]
            ]

prop_e2eReplayAndTamper :: Property
prop_e2eReplayAndTamper = once $
  conjoin
    [ replayThenTamper
        "ord@1"
        (ordE2EArg "(ordcmp (prem e1) (prem e2))")
        -- one byte: the right slot's numeral, so the right cell no longer
        -- matches the goal numeral
        (ordcmp (prem "0") (prem "0"))
    , replayThenTamper
        "ra@1"
        (raE2EArg "(radrop (prem eA) (prem eB) (frac 119 500))")
        -- one byte: the witness denominator (119/501 is still lowest-terms
        -- wire form, so this is a replay rejection, not a decode error)
        (SList [SAtom "radrop", prem "0", prem "1", SList [SAtom "frac", SAtom "119", SAtom "501"]])
    ]

-- ---------------------------------------------------------------------------
-- End-to-end: nd@1 untouched
-- ---------------------------------------------------------------------------

-- | The @nd\@1@ accept path is byte-for-byte the pre-change one: the S1-shaped
-- @(hyp 0)@ certificate elaborates, replays, and justifies its claim.
prop_ndE2EHypAccepts :: Property
prop_ndE2EHypAccepts = once $
  case e2eVerdict (ndE2EArg "(hyp 0)") of
    Left err -> counterexample err False
    Right verdict ->
      case verdictOutcome verdict of
        Reject rejection -> counterexample ("unexpected reject " ++ show rejection) False
        outcome@Accept{} ->
          conjoin
            [ counterexample "nd@1 certified arg not in" $
                verdictLabels outcome === [(0, LIn)]
            , counterexample "c_cite not justified" $
                map snd (verdictStatuses outcome)
                  === [Published Gap, Published Gap, Published Justified]
            ]

-- | An adversarial marker-free @nd\@1@ payload reaches the wire byte-identical
-- to its authored spelling, and its verdict is still the R13 the nd decoder
-- owns. Named markers are now lowered or refused by the presentation pass.
--
-- Reachability boundary: no ACCEPTING @nd\@1@ fixture can carry the spurious
-- node, because @nd\@1@'s closed decoder owns the whole payload and @prem@ is
-- not in its tag table ("Lara.Strict.ND") — any payload containing it is an
-- R13 before proof checking. What is reachable, and pinned here, is the two
-- halves of "untouched": pass-through to the exact wire bytes, and the same
-- rejection the pre-change pipeline produced.
prop_ndE2EAdversarialPayloadUntouched :: Property
prop_ndE2EAdversarialPayloadUntouched = once $
  case e2eElaborated decls of
    Left err -> counterexample err False
    Right (_, _, unit) ->
      conjoin
        [ counterexample "elaborated payload differs from the authored one" $
            (payloadOf =<< lookup (ArgId "a_cite") (unitArgs unit)) === Just authored
        , counterexample "authored payload bytes absent from the encoded unit" $
            property (payloadText `isInfixOf` printSExpr (encodeUnit unit))
        , case e2eVerdict decls of
            Left err -> counterexample err False
            Right verdict ->
              counterexample "adversarial nd@1 payload must reject R13" $
                verdictOutcome verdict === Reject (RejectClass R13)
        ]
  where
    payloadText = "(app (hyp 0) (hyp 0))"
    decls = ndE2EArg payloadText
    authored =
      SList
        [ SAtom "app"
        , SList [SAtom "hyp", SAtom "0"]
        , SList [SAtom "hyp", SAtom "0"]
        ]

-- ---------------------------------------------------------------------------
-- End-to-end: the printer round-trip (D7 — zero parser changes)
-- ---------------------------------------------------------------------------

-- | @parse (print program) == program@ for the symbolic twins, and the printed
-- text still carries the authored symbolic spelling — a named slot survives
-- print\/reparse as itself, never as its lowered numeral.
prop_symbolicSpellingPrintRoundTrips :: Property
prop_symbolicSpellingPrintRoundTrips = once $
  conjoin
    [ roundTrip
        "ord@1 twin"
        "(prem e1)"
        (certProgramSource (pairArg "(ordcmp (prem e1) (prem e2))"))
    , roundTrip
        "ra@1 twin"
        "(prem eA)"
        (e2eProgramSource (raE2EArg "(radrop (prem eA) (prem eB) (frac 119 500))"))
    ]
  where
    roundTrip what spelling source =
      case parseProgram source of
        Left err -> counterexample (what ++ ": fixture parse failed: " ++ show err) False
        Right program ->
          conjoin
            [ counterexample (what ++ ": print/reparse drifted") $
                parseProgram (printProgram program) === Right program
            , counterexample (what ++ ": authored spelling lost in print") $
                property (spelling `isInfixOf` printProgram program)
            ]

-- ---------------------------------------------------------------------------
-- Diagnostics
-- ---------------------------------------------------------------------------

-- | Exact wording for every certificate-slot failure. These strings are the
-- author-facing contract, so they are pinned character-for-character.
prop_certSlotDiagnosticMessages :: Property
prop_certSlotDiagnosticMessages = once $
  conjoin
    [ counterexample "unresolved wording drifted" $
        elabErrorMessage (CertSlotUnresolved (ArgId "a1") (AST.BackendId "ord") 1 (AST.ArgRef "e4") (RuleId "pair"))
          === "arg 'a1': certificate 'ord@1' premise reference 'e4' names neither a premise label of rule 'pair', a declared leaf, nor a prior argument"
    , counterexample "label-ambiguous wording drifted" $
        elabErrorMessage (CertSlotLabelAmbiguous (ArgId "a1") (AST.BackendId "ord") 1 (AST.ArgRef "e4") (RuleId "pair"))
          === "arg 'a1': certificate 'ord@1' premise reference 'e4' is ambiguous between rule 'pair' premise label and a declared leaf or prior argument"
    , counterexample "ambiguous wording drifted" $
        elabErrorMessage (CertSlotAmbiguous (ArgId "a1") (AST.BackendId "ord") 1 (AST.ArgRef "e4"))
          === "arg 'a1': certificate 'ord@1' premise reference 'e4' is ambiguous between a declared leaf and a prior argument"
    , counterexample "not-a-premise wording drifted" $
        elabErrorMessage (CertSlotNotAPremise (ArgId "a1") (AST.BackendId "ord") 1 (AST.ArgRef "e4"))
          === "arg 'a1': certificate 'ord@1' premise reference 'e4' does not resolve to any of this argument's premise slots"
    , counterexample "labelled multi-slot wording drifted" $
        certErrorMessage (twinArg "(ordcmp (prem e1) (prem 1))")
          === Right "arg 'a_twin': certificate 'ord@1' premise reference 'e1' occupies premise slots 0 and 1; cite a numeric slot or the rule's premise label for the slot you mean"
    , counterexample "unlabelled multi-slot wording drifted" $
        certErrorMessage (plainTwinArg "(ordcmp (prem e1) (prem 1))")
          === Right "arg 'a_plain_twin': certificate 'ord@1' premise reference 'e1' occupies premise slots 0 and 1; cite a numeric slot"
    , counterexample "non-canonical-numeral wording drifted" $
        elabErrorMessage (CertSlotNonCanonicalNumeral (ArgId "a1") (AST.BackendId "ord") 1 (AST.ArgRef "007"))
          === "arg 'a1': certificate 'ord@1' premise reference '007' is not a canonical slot numeral (use unsigned decimal with no leading zeros); write the canonical numeral or a source name"
    , counterexample "schema-mismatch wording drifted" $
        elabErrorMessage (CertSlotSchemaMismatch (ArgId "a1") (AST.BackendId "ord") 1 (AST.ArgRef "e4"))
          === "arg 'a1': certificate 'ord@1' payload does not match the backend's premise-reference schema but contains symbolic premise reference 'e4'"
    ]

certSlotsSpecProps :: [(String, IO Result)]
certSlotsSpecProps =
  [ ("ord@1 schema matches the ordcmp wire grammar", quickCheckResult prop_ordSchemaMatchesWireGrammar)
  , ("ra@1 schema matches the radrop wire grammar", quickCheckResult prop_raSchemaMatchesWireGrammar)
  , ("every declared reference slot is inside the payload arity", quickCheckResult prop_refSlotsInsideArity)
  , ("schema keys are pairwise distinct", quickCheckResult prop_schemaKeysDistinct)
  , ("lowers symbolic ord refs to numeric slots", quickCheckResult prop_lowersSymbolicOrdRefs)
  , ("accepts mixed symbolic/numeric positions", quickCheckResult prop_acceptsMixedPositions)
  , ("lowers a non-ASCII source identifier through the resolver", quickCheckResult prop_lowersUnicodeIdentifierRef)
  , ("leaves numeric payloads untouched", quickCheckResult prop_leavesNumericPayloadsUntouched)
  , ("rejects non-canonical numerals with the dedicated error", quickCheckResult prop_rejectsNonCanonicalNumerals)
  , ("reports each resolver failure with the offending name", quickCheckResult prop_reportsResolverFailures)
  , ("passes ra@1 witness fractions through while lowering its two refs", quickCheckResult prop_lowersRaRefsAroundWitness)
  , ("passes schema-less and symbolic-free mismatched payloads through byte-identical", quickCheckResult prop_passesMismatchesWithoutSymbolsThrough)
  , ("rejects symbolic names inside schema-mismatched payloads of a schema'd backend", quickCheckResult prop_rejectsSymbolsInMismatchedPayloads)
  , ("leaves a non-(prem ...) node at a reference position for the backend", quickCheckResult prop_leavesNonPremNodeAtRefPosition)
  , ("is the identity on any payload containing no symbolic (prem s) anywhere", quickCheckResult prop_identityOnSymbolicFreePayloads)
  , ("a symbolic certificate elaborates to the numeric twin's Unit", quickCheckResult prop_symbolicTwinMatchesNumeric)
  , ("the inferred spelling lowers to the same Unit as the explicit one", quickCheckResult prop_inferredSpellingLowersIdentically)
  , ("mixed symbolic/numeric positions lower position-wise", quickCheckResult prop_mixedSpellingLowers)
  , ("a prior-argument citation lowers in both spellings", quickCheckResult prop_priorArgumentCitationBothSpellings)
  , ("a premise-label citation elaborates to the numeric twin's Unit", quickCheckResult prop_labelCitationLowersToNumericTwin)
  , ("labels cite the two slots one leaf fills, where the leaf name cannot", quickCheckResult prop_labelResolvesMultiSlot)
  , ("partial premise labels do not advertise an unavailable multi-slot repair", quickCheckResult prop_partialLabelsDoNotAdvertiseUnavailableRepair)
  , ("all matching slots need labels before multi-slot label repair is advertised", quickCheckResult prop_allMatchingSlotsNeedLabels)
  , ("shadowed premise labels do not advertise an unavailable repair", quickCheckResult prop_shadowedLabelDoesNotAdvertiseUnavailableRepair)
  , ("a label colliding with a declared leaf is a hard error", quickCheckResult prop_labelLeafCollisionIsHardError)
  , ("a label colliding with a prior argument is a hard error", quickCheckResult prop_labelPriorArgumentCollisionIsHardError)
  , ("a label whose slot the authored premise list lacks is refused", quickCheckResult prop_labelSlotOutsideAuthoredPremises)
  , ("the unresolved verdict names the rule and all three name classes", quickCheckResult prop_unresolvedNamesAllThreeClasses)
  , ("an unlabelled rule resolves exactly as it did at @0.6", quickCheckResult prop_unlabelledRuleResolvesAsBefore)
  , ("certificate slot failures are fail-closed and located", quickCheckResult prop_certSlotFailureMatrix)
  , ("the inferred spelling rejects an unresolved slot name", quickCheckResult prop_inferredSpellingRejectsUnresolved)
  , ("a marker-free nd@1 payload is untouched", quickCheckResult prop_schemalessBackendUntouched)
  , ("a nested instance's certificate lowers against its own premises", quickCheckResult prop_lowersNestedCertificate)
  , ("premise labels are scoped to the citing instance's own rule", quickCheckResult prop_nestedCertificateLabelScope)
  , ("both prior-argument premise representations resolve", quickCheckResult prop_priorArgumentPremiseSpellingsAgree)
  , ("certificate slot diagnostics carry their exact wording", quickCheckResult prop_certSlotDiagnosticMessages)
  , ("ord@1 twins encode to byte-identical wire units", quickCheckResult prop_ordTwinsEncodeByteIdentical)
  , ("ra@1 twins encode to byte-identical wire units", quickCheckResult prop_raTwinsEncodeByteIdentical)
  , ("ord@1 end-to-end twins produce byte-identical accept verdicts", quickCheckResult prop_ordE2EVerdictIdentity)
  , ("ra@1 end-to-end twins produce byte-identical accept verdicts", quickCheckResult prop_raE2EVerdictIdentity)
  , ("the lowered unit replays; a tampered payload byte rejects R13", quickCheckResult prop_e2eReplayAndTamper)
  , ("nd@1 end-to-end: the (hyp 0) certificate still accepts", quickCheckResult prop_ndE2EHypAccepts)
  , ("nd@1 marker-free adversarial payload reaches the wire untouched and rejects R13", quickCheckResult prop_ndE2EAdversarialPayloadUntouched)
  , ("the authored symbolic spelling survives the printer round-trip", quickCheckResult prop_symbolicSpellingPrintRoundTrips)
  ]
