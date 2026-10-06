module Lara.Evidence.JSON (JsonValue (..), ValidatedJSON, decodeJSON, decodeValidatedJSON, selectJSON, validateJSON, selectValidatedJSON) where

import Control.Monad (unless)
import qualified Data.ByteString as B
import Data.Char (chr, digitToInt, isHexDigit, ord)
import Data.List (stripPrefix)
import qualified Data.Set as Set
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Lara.Evidence.Decimal
import Lara.Evidence.Types
import Lara.Prop
import Lara.Strict.Cell (parseCanonicalNat)

data JsonValue = JsonObject [(JsonToken,JsonValue)] | JsonArray [JsonValue]
  | JsonString String | JsonNumber String | JsonBool Bool | JsonNull deriving (Eq,Show)

decodeValidatedJSON :: B.ByteString -> Either String ValidatedJSON
decodeValidatedJSON bytes = ValidatedJSON <$> decodeJSON bytes

decodeJSON :: B.ByteString -> Either String JsonValue
decodeJSON bytes = do
  unless (B.length bytes <= 8*1024*1024) (Left "object size bound exceeded")
  s <- either (const (Left "JSON is not strict UTF8")) (Right . T.unpack) (T.decodeUtf8' bytes)
  (v,rest,_) <- value 0 0 s
  unless (null (ws rest)) (Left "trailing JSON input")
  pure v
  where
    ws = dropWhile (`elem` " \t\r\n")
    value depth count input = do
      unless (depth <= 128) (Left "JSON depth bound exceeded")
      unless (count < 100000) (Left "JSON node bound exceeded")
      let n = count+1
      case ws input of
        '"':s -> do (str,rest) <- string [] s; pure (JsonString str,rest,n)
        '{':s -> object depth n Set.empty [] (ws s)
        '[':s -> array depth n [] (ws s)
        s | Just rest <- stripPrefix "true" s -> Right (JsonBool True,rest,n)
          | Just rest <- stripPrefix "false" s -> Right (JsonBool False,rest,n)
          | Just rest <- stripPrefix "null" s -> Right (JsonNull,rest,n)
          | otherwise -> do (lexeme,rest) <- number s; pure (JsonNumber lexeme,rest,n)
    object _ n _ entries ('}':rest) = Right (JsonObject (reverse entries),rest,n)
    object depth n seen entries ('"':s) = do
      (key,afterKey) <- string [] s
      unless (key `Set.notMember` seen) (Left "duplicate JSON key")
      afterColon <- case ws afterKey of ':':r -> Right r; _ -> Left "missing JSON colon"
      (v,afterValue,n') <- value (depth+1) n afterColon
      let entries' = (JsonToken key,v):entries
      case ws afterValue of
        '}':r -> Right (JsonObject (reverse entries'),r,n')
        ',':r -> case ws r of '"':_ -> object depth n' (Set.insert key seen) entries' (ws r); _ -> Left "invalid JSON object entry"
        _ -> Left "invalid JSON object separator"
    object _ _ _ _ _ = Left "invalid JSON object"
    array _ n values (']':rest) = Right (JsonArray (reverse values),rest,n)
    array depth n values s = do
      (v,after,n') <- value (depth+1) n s
      case ws after of
        ']':r -> Right (JsonArray (reverse (v:values)),r,n')
        ',':r -> case ws r of ']':_ -> Left "trailing JSON comma"; rest -> array depth n' (v:values) rest
        _ -> Left "invalid JSON array separator"
    string acc ('"':rest) = Right (reverse acc,rest)
    string acc ('\\':s) = case s of
      '"':r -> string ('"':acc) r
      '\\':r -> string ('\\':acc) r
      '/':r -> string ('/':acc) r
      'b':r -> string ('\b':acc) r
      'f':r -> string ('\f':acc) r
      'n':r -> string ('\n':acc) r
      'r':r -> string ('\r':acc) r
      't':r -> string ('\t':acc) r
      'u':r -> do
        (u,rest) <- hex4 r
        if u >= 0xd800 && u <= 0xdbff
          then case rest of
            '\\':'u':r2 -> do
              (lo,r3) <- hex4 r2
              unless (lo >= 0xdc00 && lo <= 0xdfff) (Left "invalid JSON surrogate pair")
              string (chr (0x10000+(u-0xd800)*1024+lo-0xdc00):acc) r3
            _ -> Left "missing JSON low surrogate"
          else if u >= 0xdc00 && u <= 0xdfff then Left "unpaired JSON low surrogate"
          else string (chr u:acc) rest
      _ -> Left "invalid JSON escape"
    string acc (c:s) | ord c >= 32 = string (c:acc) s
    string _ _ = Left "invalid JSON string"
    hex4 s = let (digits,rest) = splitAt 4 s in
      if length digits == 4 && all isHexDigit digits then Right (foldl (\n c -> n*16+digitToInt c) 0 digits,rest) else Left "invalid JSON Unicode escape"
    number s = do
      let (sign,r0) = case s of '-':r -> ("-",r); _ -> ("",s)
      (whole,r1) <- case r0 of
        '0':r -> Right ("0",r)
        c:_ | c >= '1' && c <= '9' -> Right (span digit r0)
        _ -> Left "invalid JSON number"
      (frac,r2) <- case r1 of
        '.':r -> let (ds,rest)=span digit r in if null ds then Left "invalid JSON fraction" else Right ('.':ds,rest)
        _ -> Right ("",r1)
      (expo,r3) <- case r2 of
        e:r | e `elem` "eE" -> let (sgn,body)=case r of '+':t -> ("+",t); '-':t -> ("-",t); _ -> ("",r)
                                   (ds,rest)=span digit body
                               in if null ds then Left "invalid JSON exponent" else Right (e:sgn++ds,rest)
        _ -> Right ("",r2)
      pure (sign++whole++frac++expo,r3)
    digit c = c >= '0' && c <= '9'

newtype ValidatedJSON = ValidatedJSON JsonValue
validateJSON :: JsonValue -> Either String ValidatedJSON
validateJSON root = do
  _ <- validate (0 :: Int) (0 :: Int) root
  pure (ValidatedJSON root)
  where
    validate depth count v = do
      unless (depth <= 128 && count < 100000) (Left "JSON structure bound exceeded")
      case v of
        JsonObject es -> do
          unless (length es == Set.size (Set.fromList (map fst es))) (Left "duplicate JSON key")
          foldChildren depth (count+1) (map snd es)
        JsonArray vs -> foldChildren depth (count+1) vs
        _ -> Right (count+1)
    foldChildren _ count [] = Right count
    foldChildren depth count (v:vs) = do n <- validate (depth+1) count v; foldChildren depth n vs

selectJSON :: JsonValue -> [JsonSelector] -> Pred -> Either String Prop
selectJSON root selectors predicate =
  validateJSON root >>= \validated -> selectValidatedJSON validated selectors predicate
selectValidatedJSON :: ValidatedJSON -> [JsonSelector] -> Pred -> Either String Prop
selectValidatedJSON (ValidatedJSON root) selectors predicate = do
  unless (length selectors <= 256) (Left "selector bound exceeded")
  terms <- mapM one selectors
  pure (nf (Prop predicate terms))
  where
    one (JsonSelector path enc) = do
      v <- resolve root path
      case (enc,v) of
        (Decimal,JsonNumber n) -> decimalTerm n
        (Text,JsonString s) -> Right (TStr s)
        (DecimalLine,JsonString s) -> case reverse s of
          '\n':rest -> decimalTerm (reverse rest)
          _ -> Left "decimal-line requires exactly one terminal LF"
        _ -> Left "wrong JSON scalar type"
    resolve v [] = Right v
    resolve (JsonObject es) (key:rest) = maybe (Left "missing JSON pointer") (\v -> resolve v rest) (lookup key es)
    resolve (JsonArray vs) (JsonToken key:rest)
      | length key > length (show size) = Left "invalid JSON array index"
      | otherwise = case parseCanonicalNat key of
          Just i | i < toInteger size -> resolve (vs !! fromInteger i) rest
          _ -> Left "invalid JSON array index"
      where size = length vs
    resolve _ _ = Left "missing JSON pointer"
