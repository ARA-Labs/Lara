-- | Run the @>>>@ examples in the library's Haddock comments.
--
-- doctest works by standing in for GHC inside @cabal repl@, so the library is
-- loaded with exactly the build plan and language extensions the cabal file
-- gives it. This suite exists so that the @doctest@ executable is a declared
-- @build-tool-depends@ of the package: cabal builds it into the store with
-- everything else, the freeze file pins it, and CI's store cache carries it,
-- instead of a separate @cabal install@ on every machine and runner.
--
-- The nested @cabal repl@ needs the package directory as its working
-- directory; @cabal test@ guarantees that.
module Main (main) where

import System.Exit (exitWith)
import System.Process (proc, waitForProcess, withCreateProcess)

main :: IO ()
main = do
  let cmd = proc "cabal" ["repl", "lib:lara", "--with-ghc=doctest", "--repl-options=-w -Wdefault"]
  code <- withCreateProcess cmd $ \_ _ _ handle -> waitForProcess handle
  exitWith code
