module Lara.Evidence.Syntax
  ( encodeRequest, decodeRequest, encodeCheckers, decodeCheckers, parsePointer, renderPointer
  ) where

import Control.Monad (unless)
import Data.List (intercalate, nub)
import Lara.Evidence.Types
import Lara.Prop (Pred (..))
import Lara.Strict (SExpr (..))
import Lara.Strict.Cell (parseCanonicalNat)

encodeRequest :: ExtractionRequest -> SExpr
encodeRequest r = case r of
  CsvRowRequest (CheckerVersion v) (ObjectId o) (ColumnName k) raw sels (Pred p) ->
    SList [SAtom (checkerText CsvRow), SAtom (show v), SAtom o, SList [SAtom "key",SAtom k,SAtom raw], SList (SAtom "select" : [SList [SAtom c,SAtom (encodingText e)] | CsvSelector (ColumnName c) e <- sels]), predicate p]
  JsonPointerRequest (CheckerVersion v) (ObjectId o) sels (Pred p) ->
    SList [SAtom (checkerText JsonPointer), SAtom (show v), SAtom o, SList (SAtom "select" : [SList [SAtom (renderPointer path),SAtom (encodingText e)] | JsonSelector path e <- sels]), predicate p]
  where predicate p = SList [SAtom "predicate",SAtom p]

decodeRequest :: SExpr -> Either String ExtractionRequest
decodeRequest expr = case expr of
  SList [SAtom c,SAtom v,SAtom o,SList [SAtom "key",SAtom k,SAtom raw],SList (SAtom "select":sels),SList [SAtom "predicate",SAtom p]] | parseChecker c == Just CsvRow -> do
    version <- decodeVersion v
    boundedSelectors sels
    selected <- mapM csvSel sels
    pure (CsvRowRequest version (ObjectId o) (ColumnName k) raw selected (Pred p))
  SList [SAtom c,SAtom v,SAtom o,SList (SAtom "select":sels),SList [SAtom "predicate",SAtom p]] | parseChecker c == Just JsonPointer -> do
    version <- decodeVersion v
    boundedSelectors sels
    selected <- mapM jsonSel sels
    pure (JsonPointerRequest version (ObjectId o) selected (Pred p))
  _ -> Left "malformed extraction request"
  where
    csvSel (SList [SAtom c,SAtom e]) = do
      enc <- encoding e
      unless (enc /= DecimalLine) (Left "decimal-line is JSON-only")
      pure (CsvSelector (ColumnName c) enc)
    csvSel _ = Left "malformed CSV selector"
    jsonSel (SList [SAtom p,SAtom e]) = JsonSelector <$> parsePointer p <*> encoding e
    jsonSel _ = Left "malformed JSON selector"
    encoding e = maybe (Left "unknown term encoding") Right (parseEncoding e)

boundedSelectors :: [a] -> Either String ()
boundedSelectors xs = unless (length xs <= 256) (Left "selector bound exceeded")

decodeVersion :: String -> Either String CheckerVersion
decodeVersion s = maybe (Left "checker version must be a canonical natural") (Right . CheckerVersion) (parseCanonicalNat s)

encodeCheckers :: [(LeafCheckerId,CheckerVersion)] -> SExpr
encodeCheckers cs = SList (SAtom "checkers" : [SList [SAtom (checkerText c),SAtom (show v)] | (c,CheckerVersion v) <- cs])
decodeCheckers :: SExpr -> Either String [(LeafCheckerId,CheckerVersion)]
decodeCheckers (SList (SAtom "checkers":xs)) = do
  cs <- mapM one xs
  unless (length cs == length (nub cs)) (Left "duplicate evidence checker entry")
  pure cs
  where
    one (SList [SAtom c,SAtom v]) = (,) <$> maybe (Left "unknown evidence checker") Right (parseChecker c) <*> decodeVersion v
    one _ = Left "malformed evidence checker entry"
decodeCheckers _ = Left "malformed evidence checker allowlist"

parsePointer :: String -> Either String JsonPath
parsePointer "" = Right []
parsePointer ('/':s) = mapM (fmap JsonToken . unescape) (split s)
  where
    split t = case break (== '/') t of
      (a,[]) -> [a]
      (a,_:b) -> a:split b
    unescape [] = Right []
    unescape ('~':'0':rest) = ('~':) <$> unescape rest
    unescape ('~':'1':rest) = ('/':) <$> unescape rest
    unescape ('~':_) = Left "invalid JSON pointer escape"
    unescape (c:rest) = (c:) <$> unescape rest
parsePointer _ = Left "JSON pointer must be empty or begin with '/'"
renderPointer :: JsonPath -> String
renderPointer [] = ""
renderPointer xs = '/' : intercalate "/" [concatMap escape s | JsonToken s <- xs]
  where escape '~' = "~0"; escape '/' = "~1"; escape c = [c]
