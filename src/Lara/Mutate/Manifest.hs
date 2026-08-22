-- | The @MANIFEST.tsv@ contract of the generated mutation suite: where each
-- mutant file lives under the suite root, and the TSV rows that describe them.
--
-- The column order is frozen, not incidental. @scripts\/differential.sh@
-- hardcodes the expected column as @$5@ and the two 'Lara.Mutate.codecDiagnostics'
-- deletion-sensitivity pins as @$6@\/@$7@, and @test\/MutationSpec.hs@ pins the
-- whole rendering against the committed file. A new column must therefore be
-- /appended/ as column 9 or later; inserting one earlier silently rewires the
-- differential driver.
--
-- The other invariant is the split of the suite into halves: 'mutantPath'
-- routes exactly the codec-corruption family into @malformed\/@, the negative
-- half where both drivers must exit 2 with no verdict, and everything else to
-- the verdict-bearing root.
module Lara.Mutate.Manifest
  ( mutantPath
  , manifestFor
  ) where

import Lara.Diagnostics (constituentText)
import Lara.Mutate
  ( Expected (..)
  , Mutant (..)
  , codecDiagnostics
  , expectedText
  , opFamily
  , opName
  )

-- | Where a mutant lives relative to the suite root: codec-corruption
-- mutants sit in the @malformed/@ negative half (both drivers must exit 2
-- with no verdict), every other mutant is a verdict-bearing anchor.
mutantPath :: Mutant -> FilePath
mutantPath m = case mutantExpected m of
  ExpectCodecReject -> "malformed/" ++ mutantName m
  _ -> mutantName m

-- | Render the manifest rows for a mutant list (TSV: file, base, family,
-- operator, expected, hs-diagnostic, lean-diagnostic, expected-location). The
-- diagnostic columns are the 'codecDiagnostics' deletion-sensitivity pins —
-- non-empty exactly for the codec-corruption rows. @expected-location@ is the
-- seeded ground-truth constituent ('mutantSite'), appended as column 8 (@-@
-- when there is no single seeded site); it is appended, never inserted earlier,
-- because @scripts\/differential.sh@ hardcodes the expected column (@$5@) and
-- the diagnostic pins (@$6@\/@$7@).
manifestFor :: [Mutant] -> String
manifestFor ms =
  unlines
    ( "# file\tbase\tfamily\toperator\texpected\ths-diagnostic\tlean-diagnostic\texpected-location"
        : [ mutantPath m
              ++ "\t"
              ++ mutantBase m
              ++ "\t"
              ++ opFamily (mutantOp m)
              ++ "\t"
              ++ opName (mutantOp m)
              ++ "\t"
              ++ expectedText (mutantExpected m)
              ++ "\t"
              ++ hsDiag
              ++ "\t"
              ++ leanDiag
              ++ "\t"
              ++ maybe "-" constituentText (mutantSite m)
          | m <- ms
          , let (hsDiag, leanDiag) =
                  maybe ("", "") id (codecDiagnostics (mutantOp m))
          ]
    )
