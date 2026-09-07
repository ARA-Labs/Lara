-- | Named certificate premise slots (lara-syntax\@0.6, #105): the pure
-- lowering pass sitting in the presentation layer __above__ the opaque
-- strict certificate. An @ord\@1@ or @ra\@1@ certificate may cite a premise
-- by its source name — @(prem e4)@ instead of @(prem 0)@ — and this pass
-- rewrites exactly those references to the byte-identical numeric payload
-- the backend already decodes. At @lara-syntax\@0.8@ (#131) the name a
-- reference may carry also includes the citing rule's declared /premise
-- label/, which names the slot itself rather than the term filling it; the
-- name scope stays entirely the caller's, so that extension shows up here
-- only as one more 'SlotRefError' verdict.
--
-- Payloads stay backend-owned. The pass consults only a backend's declared
-- flat 'SlotSchema' — head keyword, arity, and reference positions — and
-- learns no other backend grammar: only schema-declared reference positions
-- are rewritten, and a payload with no schema (nd\@1's recursive proof
-- terms, unknown backends) passes through byte-identical, so every frozen
-- artifact and every backend rejection path is preserved. The one exception
-- is the dead-wire rule for a payload that fails a schema match: if a
-- schema'd backend's mismatched payload contains a symbolic @(prem s)@
-- anywhere, it is rejected here rather than passed to a backend that must
-- refuse it. Under a matched schema, only declared reference positions are
-- interpreted; every other node stays backend-owned.
--
-- Where the pass sits in the pipeline:
--
-- > authored .lara → sexpLitP verbatim capture → Cert{certPayload :: SExpr} (opaque, backend-owned)
-- >   → [elaboration, after premise resolution: explicit SRule case + InferTheta case]
-- >   → lowerCertPayload + resolver
-- >       no schema match, no symbolic (prem s) (nd@1, unknown backend, wrong head/arity) → payload byte-identical
-- >       schema'd backend, mismatched payload WITH symbolic (prem s) → Left SlotSchemaMismatch
-- >       (prem s), s symbolic → resolve s vs labels∪leaves∪priors, locate in resolved prems
-- >           ok → rewrite to (prem N) ; fail → Left CertSlot* (rejected before the checker)
-- >   → Unit: declared references numeric; all other payload nodes backend-owned → encode → replay → strictCheck
module Lara.Elaborate.CertSlots
  ( SlotRefError (..)
  , slotSchemas
  , lowerCertPayload
  ) where

import Control.Applicative ((<|>))
import Control.Monad (zipWithM)

import Lara.AST (BackendId (..), Cert (..))
import Lara.Strict (SExpr (..))
import qualified Lara.Strict as Strict
import Lara.Syntax (isIdentStart)
import Lara.Strict.Cell (SlotSchema (..), Tag (TPrem), parseCanonicalNat, tagToString)
import qualified Lara.Strict.Insp as Insp
import qualified Lara.Strict.Ord as Ord
import qualified Lara.Strict.RA as RA

-- | Why a symbolic premise reference failed to lower. The first five are
-- verdicts of the caller-supplied resolver (the elaborator owns the name
-- scope; this pass never inspects it); the last two are produced by
-- 'lowerCertPayload' itself.
data SlotRefError
  = -- | the name matches no premise label, declared leaf, or prior argument
    SlotNameUnresolved
  | -- | the name denotes more than one candidate in scope
    SlotNameAmbiguous
  | -- | the name is both a rule premise label and a declared leaf or prior
    -- argument (@lara-syntax\@0.8@, #131): never silently either class, even
    -- when the two classes would agree on the slot.
    SlotNameLabelAmbiguous
  | -- | the name resolves, but not to a premise of this instance
    SlotNameNotAPremise
  | -- | the named premise occupies multiple slots: the first two 0-based
    -- witnesses, plus whether every matching slot has a premise label.
    SlotNameMultiSlot Int Int Bool
  | -- | atom cannot be a source name but is not a canonical numeral
    SlotNonCanonicalNumeral
  | -- | symbolic name in a schema-mismatched payload
    SlotSchemaMismatch
  deriving (Eq, Show)

-- | Every declared flat premise-reference schema: the closed table this
-- pass consults. A backend\@version absent here has no schema, and its
-- payloads pass through 'lowerCertPayload' byte-identical.
--
-- A backend may declare __more than one__ schema: @insp\@1@'s two family
-- shapes have distinct head keywords and arities, and 'matchSchema' selects on
-- both, so the two entries can never both match one payload.
slotSchemas :: [SlotSchema]
slotSchemas = [Insp.slotSchemaOne, Insp.slotSchemaDiff, Ord.slotSchema, RA.slotSchema]

-- | Lower one certificate's symbolic premise references to canonical
-- numeric slots, per the rules in the module header. On success the payload
-- differs from the input only at schema-declared reference positions that
-- held a symbolic @(prem s)@; an already-numeric or schema-less payload
-- comes back byte-identical.
lowerCertPayload
  :: (String -> Either SlotRefError Int) -- ^ name → 0-based premise slot
  -> Cert
  -> Either (String, SlotRefError) Cert -- ^ 'Left': (offending name, why)
lowerCertPayload resolve cert =
  case matchSchema (certBackend cert) (certVersion cert) (certPayload cert) of
    Nothing
      | backendHasSchema (certBackend cert) (certVersion cert)
      , Just s <- firstSymbolicRef (certPayload cert) ->
          Left (s, SlotSchemaMismatch)
      | otherwise -> Right cert
    Just (schema, h, args) -> do
      args' <- zipWithM (lowerAt schema resolve) [0 ..] args
      pure cert {certPayload = SList (SAtom h : args')}

-- | The schemas declared for a presentation backend name at a version. The
-- presentation 'BackendId' is name-only; the version rides separately on
-- the 'Cert', so both are matched against the schema's strict identity.
schemasFor :: BackendId -> Int -> [SlotSchema]
schemasFor (BackendId name) version =
  [ s
  | s <- slotSchemas
  , Strict.backendName (ssBackend s) == name
  , Strict.backendVersion (ssBackend s) == version
  ]

-- | Whether a backend\@version declares any schema at all. Schema'd
-- backends get the dead-wire rule; schema-less ones always pass through.
backendHasSchema :: BackendId -> Int -> Bool
backendHasSchema b v = not (null (schemasFor b v))

-- | The unique schema matching the certificate's backend\@version, head
-- keyword, and arity, with the payload split into head and arguments.
-- Anything less specific — wrong head, wrong arity, not a list — is no
-- match.
matchSchema :: BackendId -> Int -> SExpr -> Maybe (SlotSchema, String, [SExpr])
matchSchema b v (SList (SAtom h : args)) =
  case [s | s <- schemasFor b v, ssHead s == h, ssArity s == length args] of
    [schema] -> Just (schema, h, args)
    _ -> Nothing
matchSchema _ _ _ = Nothing

-- | The symbolic name of a slot-reference node: @(prem s)@ with @s@ not a
-- canonical natural. Canonical numeric references and every other node
-- carry no symbolic name.
symbolicRefName :: SExpr -> Maybe String
symbolicRefName (SList [SAtom k, SAtom s])
  | k == tagToString TPrem
  , Nothing <- parseCanonicalNat s =
      Just s
symbolicRefName _ = Nothing

-- | The first symbolic @(prem s)@ anywhere in a payload, leftmost-outermost:
-- a generic sub-tree scan with no backend grammar knowledge, used only to
-- enforce the dead-wire rule on schema-mismatched payloads.
firstSymbolicRef :: SExpr -> Maybe String
firstSymbolicRef e =
  symbolicRefName e <|> case e of
    SAtom _ -> Nothing
    SList es -> foldr ((<|>) . firstSymbolicRef) Nothing es

-- | Lower one argument position. Only a symbolic @(prem s)@ at a declared
-- reference position is touched. An atom that cannot start a source
-- identifier is a malformed numeral ('SlotNonCanonicalNumeral'); every
-- identifier-shaped atom goes to the resolver. Canonical numeric references,
-- non-@(prem …)@ nodes at reference positions, and non-reference positions
-- (e.g. @ra\@1@'s witness fraction) pass through untouched — the backend's to
-- accept or reject.
lowerAt
  :: SlotSchema
  -> (String -> Either SlotRefError Int)
  -> Int -- ^ 0-based argument position
  -> SExpr
  -> Either (String, SlotRefError) SExpr
lowerAt schema resolve i e
  | i `elem` ssRefSlots schema
  , Just s <- symbolicRefName e =
      if not (startsSourceIdentifier s)
        then Left (s, SlotNonCanonicalNumeral)
        else case resolve s of
          Right slot -> Right (SList [SAtom (tagToString TPrem), SAtom (show slot)])
          Left err -> Left (s, err)
  | otherwise = Right e

-- | The lexical first-character rule shared by every surface identifier:
-- letters and underscore begin names; every other symbolic slot atom is a
-- malformed attempt at a numeral.
startsSourceIdentifier :: String -> Bool
startsSourceIdentifier (c : _) = isIdentStart c
startsSourceIdentifier [] = False
