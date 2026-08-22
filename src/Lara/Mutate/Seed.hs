-- | The deterministic pseudo-random stream behind the mutation generators.
--
-- Every random choice in the "Lara.Mutate" namespace flows from the frozen
-- 'Lara.Mutate.mutationSeed' through a SplitMix64 stream keyed by a string —
-- normally @(base, operator)@ via 'streamFor'. That is what makes the
-- generated suite reproducible: re-running the generator over unchanged base
-- anchors reproduces the committed mutant bytes exactly.
--
-- Two invariants make the stream load-bearing rather than incidental.
-- 'pickWithStream' draws in first-draw order without repeats, so selection
-- depends on the /list order/ of the candidate sites it is handed; and the
-- stream key threads through 'Lara.Mutate.opName', so an operator's spelling
-- is part of its identity. Reordering an enumerator's output or renaming an
-- operator moves bytes.
--
-- Internal to the library: the stream is an implementation detail of mutant
-- assembly, not part of the generator's public surface.
module Lara.Mutate.Seed
  ( streamForKey
  , streamFor
  , pickWithStream
  , pickSome
  ) where

import Data.Bits (shiftR, xor)
import Data.Char (ord)
import Data.Word (Word64)

import Lara.Mutate (MutationOp, mutationSeed, opName)

-- | One SplitMix64 step: @(next state, output)@.
splitMix64 :: Word64 -> (Word64, Word64)
splitMix64 s0 =
  let s = s0 + 0x9E3779B97F4A7C15
      z1 = (s `xor` (s `shiftR` 30)) * 0xBF58476D1CE4E5B9
      z2 = (z1 `xor` (z1 `shiftR` 27)) * 0x94D049BB133111EB
   in (s, z2 `xor` (z2 `shiftR` 31))

-- | FNV-1a over a string, for keying per-@(base, operator)@ streams.
stringSeed :: String -> Word64
stringSeed = foldl step 0xCBF29CE484222325
  where
    step h c = (h `xor` fromIntegral (ord c)) * 0x100000001B3

-- | The infinite output stream of a string-keyed generator (the one place the
-- @mutationSeed@ is folded into a stream key).
streamForKey :: String -> [Word64]
streamForKey key = go (mutationSeed `xor` stringSeed key)
  where
    go s = let (s', w) = splitMix64 s in w : go s'

-- | The infinite output stream of the @(base, operator)@-keyed generator.
streamFor :: String -> MutationOp -> [Word64]
streamFor base op = streamForKey (base ++ "/" ++ opName op)

-- | Deterministically pick at most @k@ elements (first-draw order, no repeats)
-- from a list, driven by a given stream.
pickWithStream :: [Word64] -> Int -> [a] -> [a]
pickWithStream ws k xs
  | n <= k = xs
  | otherwise = [xs !! i | i <- chosen]
  where
    n = length xs
    chosen = go [] (take (16 * k) ws)
    go acc _ | length acc == k = reverse acc
    go acc [] = reverse acc
    go acc (w : rest)
      | i `elem` acc = go acc rest
      | otherwise = go (i : acc) rest
      where
        i = fromIntegral (w `mod` fromIntegral n)

-- | Deterministically pick at most @k@ elements from the applicable sites,
-- keyed by @(base, operator)@.
pickSome :: String -> MutationOp -> Int -> [a] -> [a]
pickSome base op = pickWithStream (streamFor base op)
