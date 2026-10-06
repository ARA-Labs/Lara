module Lara.Evidence.Manifest
  ( PackagePath, packagePathText, validatePackagePath, Sha256, sha256Text, decodeSha256, hashBytes
  , ObjectMeta, objectId, objectPath, objectLength, objectDigest, makeObjectMeta
  , Manifest, manifestPaper, manifestSource, manifestPolicy, manifestObjects
  , decodeManifest, encodeManifest, manifestBytes, lookupObject, objectSExpr
  ) where

import Control.Monad (unless)
import qualified Crypto.Hash.SHA256 as SHA
import qualified Data.ByteString as B
import Data.Char (intToDigit)
import Data.List (nub)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Lara.Evidence.Types
import Lara.Strict (SExpr (..))
import Lara.Strict.Cell (parseCanonicalNat)
import Lara.Wire (parseSExpr, printSExpr)

newtype PackagePath = PackagePath String deriving (Eq,Ord,Show)
packagePathText :: PackagePath -> String
packagePathText (PackagePath p) = p
validatePackagePath :: String -> Either String PackagePath
validatePackagePath p = do
  unless (case p of [] -> False; c : _ -> c /= '/' && '\0' `notElem` p) (Left "unsafe package path")
  unless (all (\x -> not (null x) && x /= "." && x /= "..") (components p)) (Left "unsafe package path component")
  unless (T.unpack (T.pack p) == p) (Left "invalid package path Unicode scalar")
  pure (PackagePath p)
  where components s = case break (== '/') s of (a,[]) -> [a]; (a,_:rest) -> a:components rest
newtype Sha256 = Sha256 String deriving (Eq,Ord,Show)
sha256Text :: Sha256 -> String
sha256Text (Sha256 s) = s
decodeSha256 :: String -> Either String Sha256
decodeSha256 s = case splitAt 7 s of
  ("sha256:",hex) | length hex == 64 && all (`elem` "0123456789abcdef") hex -> Right (Sha256 s)
  _ -> Left "invalid SHA256 spelling"
hashBytes :: B.ByteString -> Sha256
hashBytes bytes = Sha256 ("sha256:" ++ concatMap hex (B.unpack (SHA.hash bytes)))
  where hex w = [intToDigit (fromIntegral w `div` 16),intToDigit (fromIntegral w `mod` 16)]
-- Ordinary projections keep smart-constructor and decoder invariants sealed;
-- exporting a record label would permit updates even with hidden constructors.
data ObjectMeta = ObjectMeta ObjectId PackagePath Integer Sha256 deriving (Eq,Ord,Show)
objectId :: ObjectMeta -> ObjectId
objectId (ObjectMeta ident _ _ _) = ident
objectPath :: ObjectMeta -> PackagePath
objectPath (ObjectMeta _ path _ _) = path
objectLength :: ObjectMeta -> Integer
objectLength (ObjectMeta _ _ len _) = len
objectDigest :: ObjectMeta -> Sha256
objectDigest (ObjectMeta _ _ _ digest) = digest
makeObjectMeta :: ObjectId -> String -> Integer -> Sha256 -> Either String ObjectMeta
makeObjectMeta ident@(ObjectId raw) path len digest = do
  unless (not (null raw) && '\0' `notElem` raw) (Left "invalid object identifier")
  validated <- validatePackagePath path
  unless (len >= 0 && len <= 8*1024*1024) (Left "object length bound exceeded")
  unless (path `notElem` ["lara-evidence.sexp","report.sexp","core-verdict.sexp"]) (Left "manifest may not hash itself or generated reports")
  pure (ObjectMeta ident validated len digest)
data Manifest = Manifest ObjectId ObjectId ObjectId [ObjectMeta] deriving (Eq,Show)
manifestPaper :: Manifest -> ObjectId
manifestPaper (Manifest paper _ _ _) = paper
manifestSource :: Manifest -> ObjectId
manifestSource (Manifest _ source _ _) = source
manifestPolicy :: Manifest -> ObjectId
manifestPolicy (Manifest _ _ policy _) = policy
manifestObjects :: Manifest -> [ObjectMeta]
manifestObjects (Manifest _ _ _ objects) = objects
lookupObject :: Manifest -> ObjectId -> Maybe ObjectMeta
lookupObject manifest ident = case filter ((==ident) . objectId) (manifestObjects manifest) of [o] -> Just o; _ -> Nothing
objectSExpr :: ObjectMeta -> SExpr
objectSExpr o = SList [SAtom "object",SAtom raw,SAtom (packagePathText (objectPath o)),SAtom (show (objectLength o)),SAtom (sha256Text (objectDigest o))]
  where ObjectId raw = objectId o
encodeManifest :: Manifest -> SExpr
encodeManifest m = SList [SAtom "lara-evidence",SAtom "1",field "paper" (manifestPaper m),field "source" (manifestSource m),field "policy" (manifestPolicy m),SList (SAtom "objects":map objectSExpr (manifestObjects m))]
  where field k (ObjectId ident) = SList [SAtom k,SAtom ident]
manifestBytes :: Manifest -> B.ByteString
manifestBytes = T.encodeUtf8 . T.pack . (++"\n") . printSExpr . encodeManifest
decodeManifest :: B.ByteString -> Either String Manifest
decodeManifest bytes = do
  unless (B.length bytes <= 1024*1024) (Left "manifest size bound exceeded")
  s <- either (const (Left "manifest is not strict UTF8")) (Right . T.unpack) (T.decodeUtf8' bytes)
  expr <- either (Left . show) Right (parseSExpr s)
  m <- case expr of
    SList [SAtom "lara-evidence",SAtom "1",SList [SAtom "paper",SAtom p],SList [SAtom "source",SAtom src],SList [SAtom "policy",SAtom pol],SList (SAtom "objects":entries)] -> do
      unless (length entries <= 256) (Left "manifest object bound exceeded")
      os <- mapM decodeObject entries
      unless (length os == length (nub (map objectId os))) (Left "duplicate manifest object ID")
      unless (length os == length (nub (map objectPath os))) (Left "duplicate manifest path")
      unless (length (nub [p,src,pol]) == 3) (Left "global object identifiers must be distinct")
      let result = Manifest (ObjectId p) (ObjectId src) (ObjectId pol) os
      paper <- maybe (Left "missing paper object") Right (lookupObject result (ObjectId p))
      unless (packagePathText (objectPath paper) == "PAPER.md") (Left "paper path must be PAPER.md")
      _ <- maybe (Left "missing source object") Right (lookupObject result (ObjectId src))
      _ <- maybe (Left "missing policy object") Right (lookupObject result (ObjectId pol))
      pure result
    _ -> Left "malformed evidence manifest"
  unless (manifestBytes m == bytes) (Left "noncanonical evidence manifest bytes")
  pure m
  where
    decodeObject (SList [SAtom "object",SAtom ident,SAtom p,SAtom len,SAtom digest]) = do
      unless (length len <= 7) (Left "object size bound exceeded")
      n <- maybe (Left "noncanonical object length") Right (parseCanonicalNat len)
      d <- decodeSha256 digest
      makeObjectMeta (ObjectId ident) p n d
    decodeObject _ = Left "malformed manifest object"
