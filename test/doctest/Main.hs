-- | Run the @>>>@ examples in the library's Haddock comments.
--
-- The driver exports the @lib:lara@ repl session — exact build plan,
-- language extensions, and package flags from the cabal file — as GHC
-- multi-repl unit files, then runs the @doctest@ build-tool over them.
-- This mirrors what doctest's own @cabal-doctest@ wrapper does on
-- GHC >= 9.4:
--
-- > cabal repl lib:lara --repl-multi-file DIR
-- > doctest --no-magic -unit @DIR/…-inplace …
--
-- Standing doctest up as the repl compiler via
-- @cabal repl lib:lara --with-ghc=doctest@ — what this suite did before —
-- breaks on GHC >= 9.4 whenever cabal hands the repl program its arguments
-- in a GHC response file: the @--interactive@ inside the response file
-- bypasses doctest's top-level argument filter and is rejected by the GHC
-- API session (@doctest: unrecognized option \`--interactive\'@), which is
-- exactly how CI failed. Exporting the session keeps doctest out of the
-- repl seat, so no repl-flavored argument ever reaches it.
--
-- The export runs with its own @--builddir@ inside the temporary
-- directory: a nested @cabal repl@ reconfigures the library interactively
-- in whatever build directory it shares, and in that state @cabal exec@
-- stops exposing the library's package — later gates such as
-- @test\/walking-skeleton-golden.sh@ and @scripts\/gen-mutants.hs@ then die
-- on "Could not load module ... member of the hidden package". Isolating
-- the build directory leaves the outer project's configuration untouched.
-- Dependencies still come from the shared cabal store; only the library
-- itself is compiled into the temporary build directory.
--
-- Requires GHC >= 9.4 and cabal-install >= 3.12 (the same floor as
-- doctest's wrapper). The nested @cabal@ and the @doctest@ build-tool need
-- the package directory as their working directory; @cabal test@
-- guarantees that.
module Main (main) where

import Data.List (isSuffixOf, sort)
import System.Directory (listDirectory)
import System.Exit (ExitCode (..), exitWith)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import System.Process (proc, waitForProcess, withCreateProcess)

main :: IO ()
main = withSystemTempDirectory "lara-doctest" $ \dir -> do
  -- Have cabal write the repl session as unit files instead of starting a
  -- repl, into a build directory of its own so the outer project's
  -- configuration is never rewritten.
  run
    "cabal"
    [ "repl", "lib:lara"
    , "--builddir", dir </> "build"
    , "--keep-temp-files"
    , "--repl-multi-file", dir
    ]
  files <- filter (isSuffixOf "-inplace") . sort <$> listDirectory dir
  case files of
    [] -> fail "cabal repl --repl-multi-file wrote no *-inplace unit files"
    _ ->
      run
        "doctest"
        ("--no-magic" : concatMap (\f -> ["-unit", '@' : dir </> f]) files)

-- | Run a command, inheriting all streams, and propagate its exit code.
run :: FilePath -> [String] -> IO ()
run cmd args =
  withCreateProcess (proc cmd args) $ \_ _ _ handle ->
    waitForProcess handle >>= \code -> case code of
      ExitSuccess -> pure ()
      ExitFailure _ -> exitWith code
