-- | The codec-corruption family (R14): mutants that must not decode at all.
--
-- This family is the suite's negative half. Every other operator mutates a
-- /decoded/ 'Lara.Replay.CheckInput' and specifies a verdict; these operators
-- corrupt the wire representation itself — the parsed envelope, or for
-- @OpCodecTruncate@ the raw bytes — so that both drivers must fail
-- 'Lara.Wire.decodeCheckInputFile' with exit 2 and empty stdout, producing no
-- verdict to compare.
--
-- Two consequences follow from that, and both are already encoded elsewhere in
-- the namespace: these mutants carry no seeded ground-truth site (they render
-- @-@ in the @expected-location@ column), and 'Lara.Mutate.Manifest.mutantPath'
-- routes them into @malformed\/@. Their deletion-sensitivity pins live with the
-- operator metadata as 'Lara.Mutate.codecDiagnostics'.
--
-- The family is base-independent in structure but not in bytes: each
-- corruption is applied to one base anchor's exact committed file, so it stays
-- outside the corpus sweep.
module Lara.Mutate.Codec
  ( codecMutantsForBase
  ) where

import Lara.Strict (SExpr (..))
import Lara.Wire (parseSExpr, printSExpr)

import Lara.Mutate
  ( Expected (..)
  , Mutant (..)
  , MutationOp (..)
  , mutantFileName
  )

-- | Codec-corruption mutants of one base anchor's exact file bytes. Each is a
-- structured corruption of the parsed envelope (or, for 'OpCodecTruncate', of
-- the raw bytes) that must fail 'Lara.Wire.decodeCheckInputFile' on both
-- drivers: exit 2, empty stdout.
codecMutantsForBase :: String -> String -> [Mutant]
codecMutantsForBase base bytes = case parseSExpr bytes of
  Left _ -> []
  Right top ->
    [ Mutant (mutantFileName base op 0) base op ExpectCodecReject [] out
    | (op, mutate) <- ops
    , Just mutated <- [mutate top]
    , let out = printSExpr mutated ++ "\n"
    ]
      ++ [ Mutant
             (mutantFileName base OpCodecTruncate 0)
             base
             OpCodecTruncate
             ExpectCodecReject
             []
             (truncateBytes bytes)
         ]
  where
    ops =
      sigmaOps
        ++ [ (OpCodecJunkSection, junkSection)
           , (OpCodecCoreVersion, coreVersion)
           , (OpCodecReplayOrder, replayOrder)
           , (OpCodecTheoryMismatch, theoryMismatch)
           , (OpCodecDanglingAttack, danglingAttack)
           ]
    -- The two Sigma decoder corruptions are dedicated fixtures rather than a
    -- per-base sweep: their failure is independent of the unit payload.
    sigmaOps
      | base == "A" =
          [ (OpCodecSigmaJunk, sigmaJunk)
          , (OpCodecSigmaOrder, sigmaOrder)
          ]
      | otherwise = []
    sigmaJunk = mapSection "sigma" (\kids -> Just (kids ++ [SList [SAtom "mut_junk"]]))
    sigmaOrder (SList kids) = SList <$> swapUnit kids
    sigmaOrder _ = Nothing
    swapUnit
      ( SList
          ( SAtom "unit"
              : sigma@(SList (SAtom "sigma" : _))
              : policy@(SList (SAtom "policy" : _))
              : rest
            )
          : siblings
        ) =
        Just
          ( SList (SAtom "unit" : policy : sigma : rest)
              : siblings
          )
    swapUnit (kid : siblings) = (kid :) <$> swapUnit siblings
    swapUnit [] = Nothing
    junkSection (SList kids) = Just (SList (kids ++ [SList [SAtom "mut_junk"]]))
    junkSection _ = Nothing
    -- The fixture text moves with the core-version bump; the expectation does
    -- not. `lara-core@0.1` is retired (#91 decision 5), so it is exactly the
    -- kind of unsupported version this operator must present.
    coreVersion = mapAtom (\a -> if a == "lara-core@0.2" then "lara-core@0.1" else a)
    replayOrder (SList [ci, SList (ridTag : core : policy : rest), unit]) =
      Just (SList [ci, SList (ridTag : policy : core : rest), unit])
    replayOrder _ = Nothing
    theoryMismatch = mapSection "theories" (\kids -> Just (kids ++ [SAtom "sha256:zzz_mut"]))
    danglingAttack = mapSection "attacks" retargetFirst
    retargetFirst (SList (kind : w : SAtom _ : rest) : ks) =
      Just (SList (kind : w : SAtom "mut_missing" : rest) : ks)
    retargetFirst _ = Nothing
    truncateBytes b =
      let trimmed = reverse (dropWhile (/= ')') (reverse b))
       in case reverse trimmed of
            (')' : prefix) -> reverse prefix ++ "\n"
            _ -> b ++ "("

-- | Rewrite every atom in a tree.
mapAtom :: (String -> String) -> SExpr -> Maybe SExpr
mapAtom f = Just . go
  where
    go (SAtom a) = SAtom (f a)
    go (SList kids) = SList (map go kids)

-- | Rewrite the children of the first @(tag …)@ form found anywhere in the
-- tree; 'Nothing' when the section is absent or the rewrite declines.
mapSection :: String -> ([SExpr] -> Maybe [SExpr]) -> SExpr -> Maybe SExpr
mapSection tag f = go
  where
    go (SList (SAtom t : kids))
      | t == tag = SList . (SAtom t :) <$> f kids
    go (SList kids) = SList <$> goKids kids
    go _ = Nothing
    goKids [] = Nothing
    goKids (k : ks) = case go k of
      Just k' -> Just (k' : ks)
      Nothing -> (k :) <$> goKids ks
