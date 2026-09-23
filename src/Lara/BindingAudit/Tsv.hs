module Lara.BindingAudit.Tsv
  ( TsvError (..)
  , RefCellError (..)
  , refCellErrorMessage
  , renderTsvRow
  , parseTsv
  , renderRefsCell
  , parseRefsCell
  ) where

import Data.List (intercalate)

import Lara.AST (SourceRef (..))

data TsvError
  = TsvMissingFinalNewline
  | TsvExtraFinalNewline
  | TsvCarriageReturn Int
  | TsvBlankRow Int
  | TsvMalformedEscape Int Int (Maybe Char)
  | TsvWrongColumnCount Int Int Int
  deriving (Eq, Show)

data RefCellError
  = RefCellEmpty
  | RefCellEmptyRef Int
  | RefCellReservedRef Int
  | RefCellCommaInRef SourceRef
  deriving (Eq, Show)

refCellErrorMessage :: RefCellError -> String
refCellErrorMessage refError =
  case refError of
    RefCellEmpty -> "empty refs cell; use '-' for no refs"
    RefCellEmptyRef index -> "empty ref at position " ++ show index
    RefCellReservedRef index -> "reserved '-' ref at position " ++ show index
    RefCellCommaInRef ref -> "ref contains comma: " ++ show ref

renderTsvRow :: [String] -> String
renderTsvRow = intercalate "\t" . map escapeCell

parseTsv :: Int -> String -> Either TsvError [[String]]
parseTsv expectedColumns document
  | null document || last document /= '\n' = Left TsvMissingFinalNewline
  | length document >= 2 && document !! (length document - 2) == '\n' = Left TsvExtraFinalNewline
  | Just offset <- firstCarriageReturn document = Left (TsvCarriageReturn offset)
  | otherwise = traverse parseNumberedRow (zip [1 ..] (splitOn '\n' (init document)))
  where
    parseNumberedRow (rowNumber, rawRow)
      | null rawRow = Left (TsvBlankRow rowNumber)
      | otherwise = do
          cells <- parseRow rowNumber rawRow
          let actualColumns = length cells
          if actualColumns == expectedColumns
            then Right cells
            else Left (TsvWrongColumnCount rowNumber expectedColumns actualColumns)

renderRefsCell :: [SourceRef] -> Either RefCellError String
renderRefsCell [] = Right "-"
renderRefsCell refs = intercalate "," <$> traverse renderOne (zip [1 ..] refs)
  where
    renderOne (index, ref@(SourceRef raw))
      | null raw = Left (RefCellEmptyRef index)
      | raw == "-" = Left (RefCellReservedRef index)
      | ',' `elem` raw = Left (RefCellCommaInRef ref)
      | otherwise = Right raw

parseRefsCell :: String -> Either RefCellError [SourceRef]
parseRefsCell "-" = Right []
parseRefsCell "" = Left RefCellEmpty
parseRefsCell cell = traverse parseOne (zip [1 ..] (splitOn ',' cell))
  where
    parseOne (index, raw)
      | null raw = Left (RefCellEmptyRef index)
      | raw == "-" = Left (RefCellReservedRef index)
      | otherwise = Right (SourceRef raw)

escapeCell :: String -> String
escapeCell = concatMap escape
  where
    escape '\\' = "\\\\"
    escape '\t' = "\\t"
    escape '\r' = "\\r"
    escape '\n' = "\\n"
    escape character = [character]

parseRow :: Int -> String -> Either TsvError [String]
parseRow rowNumber = go 1 [] []
  where
    go _ current cells [] = Right (reverse (reverse current : cells))
    go column current cells ('\t' : rest) =
      go (column + 1) [] (reverse current : cells) rest
    go column current cells ('\\' : escaped : rest) =
      case escapedCharacter escaped of
        Just character -> go column (character : current) cells rest
        Nothing -> Left (TsvMalformedEscape rowNumber column (Just escaped))
    go column _ _ ['\\'] = Left (TsvMalformedEscape rowNumber column Nothing)
    go column current cells (character : rest) =
      go column (character : current) cells rest

escapedCharacter :: Char -> Maybe Char
escapedCharacter '\\' = Just '\\'
escapedCharacter 't' = Just '\t'
escapedCharacter 'r' = Just '\r'
escapedCharacter 'n' = Just '\n'
escapedCharacter _ = Nothing

firstCarriageReturn :: String -> Maybe Int
firstCarriageReturn = go 1
  where
    go _ [] = Nothing
    go offset ('\r' : _) = Just offset
    go offset (_ : rest) = go (offset + 1) rest

splitOn :: Char -> String -> [String]
splitOn delimiter = go
  where
    go input =
      case break (== delimiter) input of
        (piece, []) -> [piece]
        (piece, _ : rest) -> piece : go rest
