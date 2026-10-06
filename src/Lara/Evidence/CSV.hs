module Lara.Evidence.CSV (CsvTable (..), CsvIndex, decodeCSV, decodeCSVIndex, selectCSV, indexCSV, selectIndexedCSV) where

import Control.Monad (unless)
import qualified Data.ByteString as B
import Data.List (elemIndex, nub)
import qualified Data.Map.Lazy as Map
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Lara.Evidence.Decimal
import Lara.Evidence.Types
import Lara.Prop

data CsvTable = CsvTable [ColumnName] [[String]] deriving (Eq, Show)

decodeCSV :: B.ByteString -> Either String CsvTable
decodeCSV bytes = do
  unless (B.length bytes <= 8 * 1024 * 1024) (Left "object size bound exceeded")
  text <- either (const (Left "CSV is not strict UTF8")) (Right . T.unpack) (T.decodeUtf8' bytes)
  rows <- records (0 :: Int) [] text
  case rows of
    [] -> Left "CSV has no header"
    header:body -> do
      unless (length header <= 256) (Left "CSV column bound exceeded")
      unless (length header == length (nub header)) (Left "duplicate CSV header")
      unless (length body <= 100000) (Left "CSV row bound exceeded")
      unless (all ((== length header) . length) body) (Left "ragged CSV row")
      pure (CsvTable (map ColumnName header) body)
  where
    records _ rows "" = Right (reverse rows)
    records count rows s = do
      unless (count <= 100000) (Left "CSV row bound exceeded")
      (row,rest) <- record (1 :: Int) s
      records (count+1) (row:rows) rest
    record count s = do
      unless (count <= 256) (Left "CSV column bound exceeded")
      (cell,rest) <- field s
      case rest of
        ',':more -> do (cells,end) <- record (count+1) more; pure (cell:cells,end)
        '\n':more -> Right ([cell],more)
        '\r':'\n':more -> Right ([cell],more)
        [] -> Right ([cell],[])
        _ -> Left "invalid CSV record separator"
    field ('"':s) = quoted [] s
    field s = let (v,rest) = break (`elem` ",\n\r\"") s
              in case rest of '"':_ -> Left "quote in unquoted CSV field"; _ -> Right (v,rest)
    quoted acc ('"':'"':s) = quoted ('"':acc) s
    quoted acc ('"':s) = case s of
      [] -> Right (reverse acc,s)
      c:_ | c `elem` ",\n\r" -> Right (reverse acc,s)
      _ -> Left "garbage after closing CSV quote"
    quoted _ [] = Left "unterminated CSV quote"
    quoted acc (c:s) = quoted (c:acc) s

selectCSV :: CsvTable -> ColumnName -> String -> [CsvSelector] -> Pred -> Either String Prop
selectCSV table key raw selectors predicate =
  indexCSV table >>= \indexed -> selectIndexedCSV indexed key raw selectors predicate

-- Row lists are shared; only a requested key-column's lazy value index is built.
data CsvIndex = CsvIndex [ColumnName] (Map.Map ColumnName (Map.Map String [[String]]))
indexCSV :: CsvTable -> Either String CsvIndex
indexCSV table@(CsvTable header rows) = do
  unless (length header <= 256 && length rows <= 100000) (Left "CSV selection bound exceeded")
  unless (length header == length (nub header)) (Left "duplicate CSV header")
  unless (all ((==length header) . length) rows) (Left "ragged CSV row")
  pure (buildIndex table)
decodeCSVIndex :: B.ByteString -> Either String CsvIndex
decodeCSVIndex bytes = buildIndex <$> decodeCSV bytes
buildIndex :: CsvTable -> CsvIndex
buildIndex (CsvTable header rows) = CsvIndex header (Map.fromList
  [(column,Map.fromListWith (++) [(row !! i,[row]) | row <- rows]) | (i,column) <- zip [0..] header])

selectIndexedCSV :: CsvIndex -> ColumnName -> String -> [CsvSelector] -> Pred -> Either String Prop
selectIndexedCSV (CsvIndex header indices) key raw selectors predicate = do
  unless (length selectors <= 256) (Left "selector bound exceeded")
  values <- maybe (Left "missing CSV column") Right (Map.lookup key indices)
  row <- case Map.findWithDefault [] raw values of
    [r] -> Right r
    [] -> Left "missing CSV key row"
    _ -> Left "duplicate matching CSV rows"
  terms <- mapM (selected row) selectors
  pure (nf (Prop predicate terms))
  where
    column c = maybe (Left "missing CSV column") Right (elemIndex c header)
    selected row (CsvSelector c enc) = do
      i <- column c
      case enc of
        Decimal -> decimalTerm (row !! i)
        Text -> Right (TStr (row !! i))
        DecimalLine -> Left "decimal-line is JSON-only"
