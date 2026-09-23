-- | Same-directory atomic file replacement for generated repository artifacts.
module Lara.AtomicWrite
  ( atomicWriteFile
  , atomicWriteWith
  ) where

import Control.Exception (IOException, bracketOnError, try)
import Control.Monad (void)
import System.Directory (removeFile, renameFile)
import System.FilePath (takeDirectory, takeFileName)
import System.IO (Handle, hClose, hPutStr, openTempFile)
import System.Posix.Files (setFileMode)

-- | Write exact text bytes through 'atomicWriteWith'.
atomicWriteFile :: FilePath -> String -> IO ()
atomicWriteFile destination bytes =
  atomicWriteWith destination (`hPutStr` bytes)

-- | Populate a same-directory temporary file and atomically rename it over the
-- destination. A failing writer or rename leaves the old destination intact;
-- cleanup failures never mask the original exception. Generated files are made
-- repository-readable before the rename rather than retaining @openTempFile@'s
-- owner-only mode.
atomicWriteWith :: FilePath -> (Handle -> IO ()) -> IO ()
atomicWriteWith destination writeTemporary =
  bracketOnError
    (openTempFile directory (takeFileName destination ++ ".tmp"))
    cleanup
    ( \(temporary, handle) -> do
        writeTemporary handle
        hClose handle
        setFileMode temporary 0o644
        renameFile temporary destination
    )
  where
    directory = takeDirectory destination
    cleanup (temporary, handle) = do
      ignoreIOException (hClose handle)
      ignoreIOException (removeFile temporary)

ignoreIOException :: IO () -> IO ()
ignoreIOException action = void (try action :: IO (Either IOException ()))
