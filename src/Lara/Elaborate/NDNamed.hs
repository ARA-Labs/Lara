-- | Named proof-term lowering for the registered natural-deduction backend.
--
-- This presentation-layer pass accepts the small named extension of the
-- backend's otherwise de Bruijn-indexed certificate grammar.  It runs after
-- premise-name resolution but before strict replay, replacing source-premise
-- references, source-theory references, and named binders with ordinary
-- indices.  It neither parses nor validates formulas: annotated formulas stay
-- opaque to preserve the strict decoder's ownership of that grammar.
--
-- == Pipeline
--
-- > authored payload
-- >   → firstNamedMarker
-- >       no marker  → byte-identical payload
-- >       marker     → firstResidualMarker
-- >                     residual → NamedResidual
-- >                     none     → lowerNamedPayload
-- >                                  → strict backend decode and replay
--
-- Both scans use the same named-marker vocabulary.  The first selects named
-- mode; the second restricts that vocabulary to opaque formula positions and
-- unknown constructors before lowering.  This makes 'NamedResidual' take
-- precedence over errors caused only by named-mode selection.  Conversely, a
-- kernel-only payload, malformed or not, never enters named mode and is
-- returned structure-identically for the existing backend to judge.
module Lara.Elaborate.NDNamed
  ( NamedRefError (..)
  , NamedTag (..)
  , namedTagToString
  , firstNamedMarker
  , lowerNamedPayload
  ) where

import Control.Applicative ((<|>))

import Lara.Elaborate.CertSlots (SlotRefError (..))
import Lara.Strict (SExpr (..))
import qualified Lara.Strict.Cell as Cell
  ( Tag (TPrem)
  , parseCanonicalNat
  , parseTag
  , tagToString
  )
import qualified Lara.Strict.ND as ND
  ( Tag (..)
  , parseTag
  , tagToString
  )
import Lara.Syntax (isIdentStart)
import Lara.Wire (printSExpr)

-- | Why a named proof-term reference could not lower.  A premise-resolution
-- failure is retained as 'NamedPremSlot', while all other constructors belong
-- to this pass and distinguish a malformed named extension from an error the
-- strict backend should continue to own.
data NamedRefError
  = -- | a named premise failed in the caller-supplied premise resolver
    NamedPremSlot SlotRefError
  | -- | numeric premise slot and supplied premise count
    NamedPremOutOfRange Integer Int
  | -- | a named assumption has no enclosing matching binder
    NamedBinderUnbound
  | -- | a named binder duplicates an enclosing named binder
    NamedBinderShadowed
  | -- | a named binder collides with a resolvable premise name
    NamedBinderShadowsPremise
  | -- | a four-field abstraction has no identifier-shaped binder
    NamedMalformedBinder
  | -- | an assumption or theory index is not a canonical natural
    NamedNonCanonicalIndex
  | -- | a numeric kernel assumption appeared after named mode was selected
    NamedKernelIndex
  | -- | a named marker survived in an opaque or unknown sub-tree
    NamedResidual
  deriving (Eq, Show)

-- | The closed vocabulary owned by this named presentation extension.  The
-- existing strict tags continue to live only in 'Lara.Strict.ND.Tag', and the
-- premise-reference tag continues to live only in 'Lara.Strict.Cell.Tag'.
data NamedTag = NTThy
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The sole concrete spelling owned by 'NamedTag'.
namedTagToString :: NamedTag -> String
namedTagToString NTThy = "thy"

-- | Lower a possible named payload for the natural-deduction backend.
--
-- The resolver maps a source premise name to its zero-based slot, and the
-- premise count determines where theory slots begin in the free context.  A
-- payload without a named marker returns unchanged.  Once named mode is
-- selected, numeric kernel assumptions are forbidden: every assumption must
-- be named before lowering, while numeric premise and theory references are
-- converted with the current binder depth.
lowerNamedPayload
  :: (String -> Either SlotRefError Int) -- ^ source name → premise slot
  -> Int -- ^ number of premise slots
  -> SExpr -- ^ opaque strict payload
  -> Either (String, NamedRefError) SExpr
lowerNamedPayload resolve nPrem payload =
  case firstNamedMarker payload of
    Nothing -> Right payload
    Just _ ->
      case firstResidualMarker payload of
        Just source -> Left (source, NamedResidual)
        Nothing -> lower [] payload
  where
    lower :: [Maybe String] -> SExpr -> Either (String, NamedRefError) SExpr
    lower binders expr
      | Just source <- premiseSource expr = lowerPremise binders source
      | Just source <- theorySource expr = lowerTheory binders source
      | Just source <- hypothesisSource expr = lowerNamedHypothesis binders source
      | Just (binder, formula, body) <- namedAbstraction expr =
          lowerNamedAbstraction binders binder formula body
      | Just (formula, body) <- kernelAbstraction expr =
          lowerKernelAbstraction binders formula body
      | Just (fun, arg) <- application expr =
          SList . (SAtom (ND.tagToString ND.TApp) :) <$> sequence [lower binders fun, lower binders arg]
      | Just (formula, body) <- abort expr =
          SList . (SAtom (ND.tagToString ND.TAbort) :) . (formula :) . (: []) <$> lower binders body
      | otherwise = Right expr

    lowerPremise binders source =
      case Cell.parseCanonicalNat source of
        Just slot
          | slot < toInteger nPrem -> Right (kernelHypothesis (depth binders + slot))
          | otherwise -> Left (source, NamedPremOutOfRange slot nPrem)
        Nothing
          | startsIdent source ->
              case resolve source of
                Right slot -> Right (kernelHypothesis (depth binders + toInteger slot))
                Left err -> Left (source, NamedPremSlot err)
          | otherwise -> Left (source, NamedPremSlot SlotNonCanonicalNumeral)

    lowerTheory binders source =
      case Cell.parseCanonicalNat source of
        Just slot -> Right (kernelHypothesis (depth binders + toInteger nPrem + slot))
        Nothing -> Left (source, NamedNonCanonicalIndex)

    lowerNamedHypothesis binders source =
      case Cell.parseCanonicalNat source of
        Just _ -> Left (source, NamedKernelIndex)
        Nothing
          | startsIdent source ->
              case binderIndex source binders of
                Just index -> Right (kernelHypothesis index)
                Nothing -> Left (source, NamedBinderUnbound)
          | otherwise -> Left (source, NamedNonCanonicalIndex)

    lowerNamedAbstraction binders (SAtom binder) formula body
      | not (startsIdent binder) = Left (binder, NamedMalformedBinder)
      | Just _ <- binderIndex binder binders = Left (binder, NamedBinderShadowed)
      | Right _ <- resolve binder = Left (binder, NamedBinderShadowsPremise)
      | otherwise = do
          body' <- lower (Just binder : binders) body
          Right (SList [SAtom (ND.tagToString ND.TLam), formula, body'])
    lowerNamedAbstraction _ binder _ _ = Left (markerSource binder, NamedMalformedBinder)

    lowerKernelAbstraction binders formula body = do
      body' <- lower (Nothing : binders) body
      Right (SList [SAtom (ND.tagToString ND.TLam), formula, body'])

-- | The first named extension marker in leftmost-outermost order.  This scan
-- selects named mode; 'firstResidualMarker' narrows the same marker vocabulary
-- to positions the lowering grammar treats as opaque.
firstNamedMarker :: SExpr -> Maybe String
firstNamedMarker expr =
  markerHere expr <|> case expr of
    SAtom _ -> Nothing
    SList children -> foldr ((<|>) . firstNamedMarker) Nothing children

-- | The first marker in a position that 'lower' deliberately does not visit.
-- Formula annotations and unknown subtrees remain backend-owned, so a marker
-- there takes precedence over errors caused only by named-mode selection.
firstResidualMarker :: SExpr -> Maybe String
firstResidualMarker expr
  | Just _ <- premiseSource expr = Nothing
  | Just _ <- theorySource expr = Nothing
  | Just _ <- hypothesisSource expr = Nothing
  | Just (_, formula, body) <- namedAbstraction expr =
      firstNamedMarker formula <|> firstResidualMarker body
  | Just (formula, body) <- kernelAbstraction expr =
      firstNamedMarker formula <|> firstResidualMarker body
  | Just (fun, arg) <- application expr =
      firstResidualMarker fun <|> firstResidualMarker arg
  | Just (formula, body) <- abort expr =
      firstNamedMarker formula <|> firstResidualMarker body
  | otherwise = firstNamedMarker expr

-- | The marker at a node, if any.  Source atoms are extracted only to report
-- the same offending spelling in every presentation-layer failure.
markerHere :: SExpr -> Maybe String
markerHere expr
  | Just source <- premiseSource expr = Just source
  | Just source <- theorySource expr = Just source
  | Just source <- namedHypSource expr = Just source
  | Just (binder, _, _) <- namedAbstraction expr = Just (markerSource binder)
  | otherwise = Nothing

-- | A premise-reference node, independently of whether its atom is legal.
premiseSource :: SExpr -> Maybe String
premiseSource (SList [SAtom tag, SAtom source])
  | tag == Cell.tagToString Cell.TPrem
  , Cell.parseTag tag == Just Cell.TPrem = Just source
premiseSource _ = Nothing

-- | The named theory-reference node owned by this module's closed table.
theorySource :: SExpr -> Maybe String
theorySource (SList [SAtom tag, SAtom source])
  | parseNamedTag tag == Just NTThy = Just source
theorySource _ = Nothing

-- | A named assumption is distinguished only by its identifier-shaped atom.
-- Numeric assumptions remain kernel syntax until another marker selects named
-- mode, at which point 'lowerNamedHypothesis' rejects them deliberately.
namedHypSource :: SExpr -> Maybe String
namedHypSource expr = do
  source <- hypothesisSource expr
  if startsIdent source then Just source else Nothing

-- | The atom of any kernel assumption node.  In named mode this includes
-- numeric and malformed indices so they receive the dedicated errors.
hypothesisSource :: SExpr -> Maybe String
hypothesisSource (SList [SAtom tag, SAtom source])
  | ND.parseTag tag == Just ND.THyp = Just source
hypothesisSource _ = Nothing

-- | A four-field named abstraction.  Its binder stays as an 'SExpr' until
-- lowering so a non-atom binder gets 'NamedMalformedBinder' rather than being
-- mistaken for backend-owned syntax.
namedAbstraction :: SExpr -> Maybe (SExpr, SExpr, SExpr)
namedAbstraction (SList [SAtom tag, binder, formula, body])
  | ND.parseTag tag == Just ND.TLam = Just (binder, formula, body)
namedAbstraction _ = Nothing

-- | The source spelling carried by a marker, or a total diagnostic rendering
-- for malformed non-atom positions.
markerSource :: SExpr -> String
markerSource (SAtom source) = source
markerSource expr = printSExpr expr

-- | The three-field kernel abstraction.  Its formula remains opaque.
kernelAbstraction :: SExpr -> Maybe (SExpr, SExpr)
kernelAbstraction (SList [SAtom tag, formula, body])
  | ND.parseTag tag == Just ND.TLam = Just (formula, body)
kernelAbstraction _ = Nothing


-- | A kernel application, whose two certificate children are lowered.
application :: SExpr -> Maybe (SExpr, SExpr)
application (SList [SAtom tag, fun, arg])
  | ND.parseTag tag == Just ND.TApp = Just (fun, arg)
application _ = Nothing

-- | A kernel falsum eliminator; its formula remains opaque while its proof
-- child is lowered.
abort :: SExpr -> Maybe (SExpr, SExpr)
abort (SList [SAtom tag, formula, body])
  | ND.parseTag tag == Just ND.TAbort = Just (formula, body)
abort _ = Nothing

-- | Emit one ordinary kernel assumption index through the strict tag table.
kernelHypothesis :: Integer -> SExpr
kernelHypothesis index =
  SList [SAtom (ND.tagToString ND.THyp), SAtom (show index)]

-- | The current de Bruijn depth, including anonymous binders.
depth :: [Maybe String] -> Integer
depth = toInteger . length

-- | The innermost matching named binder, counted through anonymous binders.
binderIndex :: String -> [Maybe String] -> Maybe Integer
binderIndex sought = go 0
  where
    go _ [] = Nothing
    go index (Just name : rest)
      | name == sought = Just index
      | otherwise = go (index + 1) rest
    go index (Nothing : rest) = go (index + 1) rest

-- | The local first-character twin of 'isIdentStart'.  This module deliberately
-- exports no new lexical helper: its only concern is deciding whether an atom
-- can be handed to the caller's name resolver.
startsIdent :: String -> Bool
startsIdent (c : _) = isIdentStart c
startsIdent [] = False

-- | Parse the presentation extension's closed tag table.
parseNamedTag :: String -> Maybe NamedTag
parseNamedTag spelling =
  lookup spelling [(namedTagToString tag, tag) | tag <- [minBound .. maxBound]]
