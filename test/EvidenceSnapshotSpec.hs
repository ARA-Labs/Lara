module EvidenceSnapshotSpec (evidenceSnapshotSpecProps) where

import qualified Data.ByteString.Char8 as B
import System.Directory (createDirectory, removeFile)
import System.FilePath ((</>))
import System.Posix.Files (createSymbolicLink, createNamedPipe)
import Test.QuickCheck
import Lara.TempTree
import Lara.Evidence.Types
import Lara.Evidence.Manifest
import Lara.Evidence.Snapshot
import EvidenceFixture
import Lara.Strict (SExpr (..))
import Lara.Wire (printSExpr)

evidenceSnapshotSpecProps :: [(String,IO Result)]
evidenceSnapshotSpecProps =
  [ ("evidence: immutable capture rejects tampering, aliases, symlinks, FIFO and directories",quickCheckResult (once (ioProperty capture)))
  , ("evidence: manifest canonical bytes and path boundaries",quickCheckResult (once (ioProperty canonical)))
  ]
  where
    capture = withTempDirectory "evidence-capture" $ \root -> do
      let bytes = B.pack "id,value\none,7\n"
      B.writeFile (root </> "data.csv") bytes
      meta <- requireRight (makeObjectMeta (ObjectId "data") "data.csv" (toInteger (B.length bytes)) (hashBytes bytes))
      checked <- withPackageRoot root $ \handle -> do
        original <- captureObject handle meta >>= requireRight
        removeFile (root </> "data.csv")
        B.writeFile (root </> "data.csv") (B.pack "id,value\none,8\n")
        changed <- captureObject handle meta
        createSymbolicLink "data.csv" (root </> "alias")
        createDirectory (root </> "dir")
        B.writeFile (root </> "dir" </> "member") bytes
        createSymbolicLink "dir" (root </> "aliasdir")
        createNamedPipe (root </> "fifo") 0o600
        let pointer = B.pack "version https://git-lfs.github.com/spec/v1\n"
        B.writeFile (root </> "pointer") pointer
        pointerMeta <- requireRight (makeObjectMeta (ObjectId "pointer") "pointer" (toInteger (B.length pointer)) (hashBytes pointer))
        lfs <- captureObject handle pointerMeta
        member <- requireRight (validatePackagePath "data.csv")
        bounded <- readPackageFile handle member 3
        results <- mapM (\path -> requireRight (validatePackagePath path) >>= \p -> readPackageFile handle p 100) ["alias","aliasdir/member","dir","fifo","missing"]
        pure (conjoin [capturedBytes original === bytes, property (isLeft changed), property (isLeft lfs), property (isLeft bounded), property (all isLeft results)])
      pure (either (\e -> counterexample e False) id checked)
    canonical = withTempDirectory "evidence-manifest" $ \root -> do
      writePackage root source policy "id,value\none,7\n" []
      raw <- B.readFile (root </> "lara-evidence.sexp")
      manifest <- requireRight (decodeManifest raw)
      let duplicateManifest = case encodeManifest manifest of
            SList [tag,version,paper,src,pol,SList (objects:first:rest)] ->
              B.pack (printSExpr (SList [tag,version,paper,src,pol,SList (objects:first:first:rest)]) ++ "\n")
            _ -> B.empty
      pure (conjoin
        [ manifestBytes manifest === raw
        , property (isLeft (decodeManifest (B.cons ' ' raw)))
        , property (isLeft (decodeManifest (B.init raw)))
        , property (isLeft (decodeManifest duplicateManifest))
        , property (all (isLeft . validatePackagePath) ["", "/x", "a/../b", "a//b", "a/./b", "a/..\0suffix", "x\0y"])
        , property (isLeft (makeObjectMeta (ObjectId "large") "data" (8*1024*1024+1) (hashBytes B.empty)))
        ])
    isLeft (Left _) = True
    isLeft _ = False
