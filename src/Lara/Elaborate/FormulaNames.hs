-- | The authored spelling of the formulas an @nd\@1@ replay rejection names
-- (#148).
--
-- When a named proof term lowers cleanly and the certificate is then refused at
-- R13, the registered backend's reason is phrased over the __lowered__ image:
-- formulas appear as @FAtom (AtomId \"1:A5:holds1:L1:2…\")@, the opaque
-- 'Lara.Strict.ND.encodeAtomKey' framing. The author wrote
-- @(prop \"holds(safety_invariant, D)\")@ and a @leaf@ declaration. This module
-- recovers the pairing, so the diagnosis can be read in the vocabulary the
-- source used.
--
-- == The two sources, and why both are needed
--
-- A mismatch has two sides and they do not come from the same place. In
--
-- > application mismatch: expected FAtom (AtomId "…other_invariant…"),
-- >                       got      FAtom (AtomId "…safety_invariant…")
--
-- the @expected@ side is the author's @(prop TEXT)@ annotation, and the @got@
-- side is the conclusion of the leaf a @(prem …)@ cited — never spelled as a
-- @prop@ at all. A map built from annotations alone would explain exactly half
-- of every mismatch, which is the half that happens to be listed first. So both
-- are collected:
--
-- * 'FOAnnotation' — a @lara-syntax\@0.10@ @(prop TEXT)@ node, reported with the
--   text verbatim, because that is the string the author will recognize.
-- * 'FOLeaf' — a declared leaf's proposition, reported through
--   'Lara.Syntax.printProp' and tagged with the leaf id, which is also what
--   @slot i = leaf …@ names it (#130).
--
-- == Why this can be recovered rather than threaded
--
-- Elaboration lowers certificate payloads in place, so the checked 'Unit' no
-- longer holds the authored spellings — but 'Program', the parsed source, is
-- retained beside it in @SourceCheckInput@ and still does. Nothing has to be
-- carried out of the elaborator, nothing new reaches 'Unit', and nothing
-- reaches the wire. This is the same recovery shape
-- "Lara.Elaborate.SlotNames" uses for premise slots.
--
-- == Why it stops at the source door
--
-- These spellings exist only where a surface was authored. A raw @.sexp@ input
-- never had them, so it keeps the structural reading alone.
module Lara.Elaborate.FormulaNames
  ( FormulaOrigin (..)
  , AuthoredFormula (..)
  , authoredFormulaMap
  , formulaMappingLines
  ) where

import Data.List (findIndex, isInfixOf, isPrefixOf, nubBy, sortOn, tails)

import Lara.AST
import Lara.Elaborate.NDNamed (authoredPropAnnotations)
import Lara.Prop (nf)
import Lara.Strict (SExpr)
import qualified Lara.Strict.ND as ND (encodeAtomKey)
import Lara.Syntax (printProp)

-- | Where an authored spelling came from.
data FormulaOrigin
  = -- | a @(prop TEXT)@ annotation inside a named proof term
    FOAnnotation
  | -- | a declared leaf's proposition, by its source id
    FOLeaf LeafId
  deriving (Eq, Show)

-- | One atom key, and the spelling the source used for it.
data AuthoredFormula = AuthoredFormula
  { afKey :: String
  -- ^ the opaque 'ND.encodeAtomKey' framing the backend names it by
  , afSpelling :: String
  -- ^ the surface spelling: the annotation text verbatim, or the leaf's
  -- proposition printed
  , afOrigin :: FormulaOrigin
  }
  deriving (Eq, Show)

-- | Every atom key this source can name, paired with its authored spelling.
--
-- Annotations come first so that a proposition spelled /both/ as a @prop@
-- annotation and as a leaf reports the annotation — the author's own words for
-- the position the rejection is about — and the duplicate leaf entry is dropped.
-- Keys are unique in the result.
authoredFormulaMap :: Program -> Unit -> [AuthoredFormula]
authoredFormulaMap program unit =
  nubBy (\a b -> afKey a == afKey b) (annotations ++ leaves)
  where
    annotations =
      [ AuthoredFormula key source FOAnnotation
      | payload <- ndPayloads program
      , (key, source) <- authoredPropAnnotations payload
      ]
    leaves =
      [ AuthoredFormula (ND.encodeAtomKey (nf p)) (printProp p) (FOLeaf l)
      | (l, p) <- unitLeaves unit
      ]

-- | Every certificate payload declared in the source, in declaration order.
--
-- Deliberately not filtered to the registered @nd\@1@ identity: a payload from
-- another backend simply carries no @prop@ nodes, so
-- 'authoredPropAnnotations' returns nothing for it, and duplicating the
-- backend-identity test ('Lara.Elaborate.Internal'.@isNdCert@) here would be a
-- second place to keep it in step.
ndPayloads :: Program -> [SExpr]
ndPayloads program =
  [ certPayload cert
  | DeclArg arg <- programDecls program
  , cert <- certsOf (argInstantiation arg)
  ]
  where
    certsOf inst = case inst of
      InferTheta _ _ _ _ assurance -> certsOfAssurance assurance
      ExplicitTheta term -> certsOfTerm term
    certsOfAssurance assurance = case assurance of
      AssuranceCert cert -> [cert]
      _ -> []
    certsOfTerm term = case term of
      SLeaf _ -> []
      SRule _ _ premises _ _ assurance ->
        certsOfAssurance assurance ++ concatMap certsOfTerm premises

-- | Render the authored spelling of every formula a rejection reason names, one
-- line per key, in the order the keys occur in the reason (#148).
--
-- __Why it selects on the reason rather than printing the whole map.__ The map
-- covers the source; the reason names two or three atoms out of it. Printing
-- all of it would bury the answer in a glossary that grows with the program,
-- and the author's question is specifically \"what are the keys in the line I
-- am looking at\". Keys the map cannot explain — a theory formula, say —
-- contribute no line, which is honest: nothing authored corresponds to them.
--
-- __Why the match is on @show@ of the key.__ The backend renders formulas with
-- 'show' ("Lara.Strict.ND".@inferType@), so an atom reaches the reason as
-- @FAtom (AtomId \"…\")@ — the key in its 'show' spelling, escapes and all.
-- Matching @'show' key@ therefore compares like with like; matching the raw key
-- would miss any spelling that 'show' escapes.
--
-- Empty in, empty out — a rejection with no reason, or one naming no key this
-- source authored, adds nothing.
formulaMappingLines :: String -> [AuthoredFormula] -> [String]
formulaMappingLines reason formulas =
  [ "  formula " ++ show i ++ " = " ++ afSpelling f ++ origin (afOrigin f)
  | (i, f) <- zip [0 :: Int ..] mentioned
  ]
  where
    mentioned = sortOn occurrence [f | f <- formulas, occursIn f]
    occursIn f = show (afKey f) `isInfixOf` reason
    -- Where the key's first occurrence starts, so the lines come out in the
    -- order the reader meets the keys. Total: a key that does not occur was
    -- already filtered out, and 'maxBound' would sort it last rather than fail.
    occurrence f =
      maybe maxBound id (findIndex (isPrefixOf (show (afKey f))) (tails reason))
    origin o = case o of
      FOAnnotation -> "  (authored annotation)"
      FOLeaf (LeafId l) -> "  (leaf " ++ l ++ ")"
