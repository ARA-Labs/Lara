-- | Developer probe: print what each row of the envelope's single-defect
-- matrix actually refuses with.
--
-- The matrix property asserts only that each row is refused. This prints the
-- refusal, which is how one checks the rows are hitting the paths their names
-- claim rather than all collapsing onto one generic parse error. Not a gate.
--
--     cabal exec -w ghc-9.6.6 -- runghc-9.6.6 -itest scripts/envelope-matrix-probe.hs
module Main (main) where

import Lara.Map.Driver (decodeMapCheckInputText)
import Lara.Map.Types (MapWireError (..))
import MapSpec (envelopeDefects, readEnvelope)

main :: IO ()
main = do
  envelope <- readEnvelope
  mapM_ (probe envelope) envelopeDefects

probe :: String -> (String, String -> String) -> IO ()
probe envelope (name, defect) = do
  let mutated = defect envelope
      changed = mutated /= envelope
  putStrLn
    ( pad 42 name
        ++ (if changed then "" else "  [NO-OP!]  ")
        ++ case decodeMapCheckInputText mutated of
          Left err -> mweContext err ++ ": " ++ mweMessage err
          Right _ -> "*** ACCEPTED ***"
    )
  where
    pad n text = text ++ replicate (max 1 (n - length text)) ' '
