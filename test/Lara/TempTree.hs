-- | Throwaway directory trees for the map test modules.
--
-- "MapSpec", "MapLoadSpec", "MapLinkSpec" and "MapExampleSpec" each write
-- @.lara@ members and manifests into a scratch directory and then assert on what
-- the loader reads back, so this is exactly the helper whose misbehaviour would
-- be misread as a bug in the code under test. It used to be copied into all
-- four, each deriving its directory name from an 'System.IO.openTempFile'
-- marker (@marker ++ ".d"@) and then adopting whatever was at that path with
-- @createDirectoryIfMissing True@. Two things were wrong with that:
--
--   * the name was __derived, not reserved__ — 'System.IO.openTempFile'
--     guaranteed the marker was unused, the marker was then deleted, and
--     nothing ever reserved the @.d@ path;
--   * @createDirectoryIfMissing True@ __accepts a path that already exists__,
--     including a symlink planted there, which would turn every later fixture
--     write and member read into a write and read of some other tree.
--
-- 'withTempDirectory' uses @mkdtemp(3)@ instead: one call picks an
-- unpredictable name and creates the directory at it atomically, mode @0700@,
-- failing rather than adopting anything already present. That closes both
-- without a new test dependency (the @temporary@ package's
-- @withSystemTempDirectory@ does the same thing; @unix@ is already a test-suite
-- dependency).
--
-- The process working directory stays the package root throughout, which is
-- what gives the map tests their force: a member path that resolves at all can
-- only have been resolved against the manifest's own directory.
module Lara.TempTree
  ( withTempDirectory
  , withTree
  ) where

import Control.Exception (bracket)
import System.Directory
  ( createDirectoryIfMissing
  , getTemporaryDirectory
  , removeDirectoryRecursive
  )
import System.FilePath (takeDirectory, (</>))
import System.Posix.Temp (mkdtemp)

-- | Reserve a fresh, empty directory under the system temporary directory, run
-- the body over it, then remove it. The template is a readable prefix only; the
-- name's uniqueness comes from @mkdtemp(3)@.
withTempDirectory :: String -> (FilePath -> IO a) -> IO a
withTempDirectory template body = do
  tmp <- getTemporaryDirectory
  bracket (mkdtemp (tmp </> (template ++ "-"))) removeDirectoryRecursive body

-- | Build a directory tree from @(relative path, contents)@ pairs in a fresh
-- reserved directory, run the body over its root, then remove it.
--
-- Writing the files happens inside the body rather than in @bracket@'s acquire:
-- an exception while writing a fixture (a bad relative path, a full disk) would
-- escape an acquire that had already created the directory, and @bracket@ does
-- not release what a failed acquire left behind. Inside the body it is covered.
-- @createDirectoryIfMissing@ is correct /there/: it only ever creates
-- subdirectories of a root this process has just reserved.
withTree :: String -> [(FilePath, String)] -> (FilePath -> IO a) -> IO a
withTree template files body =
  withTempDirectory template (\root -> mapM_ (writeInto root) files >> body root)
  where
    writeInto root (path, contents) = do
      createDirectoryIfMissing True (takeDirectory (root </> path))
      writeFile (root </> path) contents
