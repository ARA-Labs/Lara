{-# LANGUAGE ForeignFunctionInterface, ScopedTypeVariables, OverloadedStrings #-}
module Lara.Evidence.Snapshot
  ( RootHandle, withPackageRoot, readPackageFile, readVerifierPolicy
  , Snapshot, CapturedObject, emptySnapshot, captureObject, insertCaptured
  , capturedMetadata, capturedBytes, snapshotLookup, snapshotMetadata
  , publishNoReplace
  ) where

import Control.Exception (IOException, bracket, bracketOnError, try)
import Control.Monad (unless)
import qualified Data.ByteString as B
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Foreign.C.Error (throwErrnoIfMinus1)
import Foreign.C.Types
import Foreign.Ptr (Ptr)
import System.FilePath (takeDirectory, takeFileName)
import System.IO (hClose)
import System.Posix.IO (closeFd, fdToHandle)
import System.Posix.Types (Fd (..))
import Lara.Evidence.Internal
import Lara.Evidence.Manifest
import Lara.Evidence.Types

foreign import ccall unsafe "lara_evidence_root" cRoot :: Ptr CChar -> CSize -> IO CInt
foreign import ccall unsafe "lara_evidence_open" cOpen :: CInt -> Ptr CChar -> CSize -> IO CInt
foreign import ccall unsafe "lara_evidence_publish" cPublish :: Ptr CChar -> CSize -> Ptr CChar -> CSize -> IO CInt
newtype RootHandle = RootHandle Fd

withPackageRoot :: FilePath -> (RootHandle -> IO a) -> IO (Either String a)
withPackageRoot root action = ioErrorText $ bracket open close action
  where
    open = RootHandle . Fd <$> withPath root (\p n -> throwErrnoIfMinus1 "open package root" (cRoot p n))
    close (RootHandle fd) = closeFd fd
withPath :: String -> (Ptr CChar -> CSize -> IO a) -> IO a
withPath path action
  | '\0' `elem` path = ioError (userError "NUL in filesystem path")
  | T.unpack (T.pack path) /= path = ioError (userError "invalid filesystem path Unicode scalar")
  | otherwise = B.useAsCStringLen (T.encodeUtf8 (T.pack path)) (\(p,n) -> action p (fromIntegral n))
ioErrorText :: forall a. IO a -> IO (Either String a)
ioErrorText action = either (Left . show) Right <$> (try action :: IO (Either IOException a))
readPackageFile :: RootHandle -> PackagePath -> Int -> IO (Either String B.ByteString)
readPackageFile (RootHandle (Fd root)) path limit = ioErrorText $ bracket open hClose (\h -> do
  bytes <- B.hGet h (limit+1)
  if B.length bytes > limit then ioError (userError "file size bound exceeded") else pure bytes)
  where
    open = bracketOnError
      (Fd <$> withPath (packagePathText path) (\p n -> throwErrnoIfMinus1 "open package member" (cOpen root p n)))
      closeFd fdToHandle

readVerifierPolicy :: FilePath -> IO (Either String B.ByteString)
readVerifierPolicy path = case validatePackagePath (takeFileName path) of
  Left err -> pure (Left err)
  Right member -> do
    result <- withPackageRoot (takeDirectory path) (\root -> readPackageFile root member (8*1024*1024))
    pure (result >>= id)

emptySnapshot :: Snapshot
emptySnapshot = Snapshot []
capturedMetadata :: CapturedObject -> ObjectMeta
capturedMetadata (CapturedObject m _) = m
capturedBytes :: CapturedObject -> B.ByteString
capturedBytes (CapturedObject _ b) = b
snapshotLookup :: Snapshot -> ObjectId -> Maybe CapturedObject
snapshotLookup (Snapshot xs) ident = case filter ((==ident) . objectId . capturedMetadata) xs of [o] -> Just o; _ -> Nothing
snapshotMetadata :: Snapshot -> [ObjectMeta]
snapshotMetadata (Snapshot xs) = map capturedMetadata xs
insertCaptured :: CapturedObject -> Snapshot -> Snapshot
insertCaptured o (Snapshot xs) = Snapshot (xs ++ [o])
captureObject :: RootHandle -> ObjectMeta -> IO (Either String CapturedObject)
captureObject root meta = do
  bytes <- readPackageFile root (objectPath meta) (fromInteger (objectLength meta))
  pure $ do
    b <- bytes
    unless (toInteger (B.length b) == objectLength meta) (Left "object length mismatch")
    unless (hashBytes b == objectDigest meta) (Left "object SHA256 mismatch")
    unless (not (B.isPrefixOf "version https://git-lfs.github.com/spec/v1" b)) (Left "unresolved Git LFS pointer")
    pure (CapturedObject meta b)

publishNoReplace :: FilePath -> FilePath -> IO ()
publishNoReplace source destination = withPath source $ \p n -> withPath destination $ \q m -> do
  _ <- throwErrnoIfMinus1 "publish evidence bundle (RENAME_NOREPLACE)" (cPublish p n q m)
  pure ()
