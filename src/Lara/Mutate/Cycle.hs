-- | The constructed rebut-cycle family: the specified /non/-rejection.
--
-- Attack N-cycles are the one Phase D mutation class whose specified outcome
-- is an accept (spec §10.1). Grounded semantics labels every member of an
-- attack cycle @undec@, so every queried claim comes back @contested@ — a
-- verdict the checker must produce rather than reject. That makes this family
-- the suite's guard against a checker that rejects too eagerly.
--
-- Unlike every other family here, these units are /constructed/ rather than
-- mutated: they derive from no base anchor, so they carry base @-@ and no
-- seeded ground-truth site. Only the cycle sizes come from the seeded stream
-- ("Lara.Mutate.Seed"), keyed at the synthetic base @-@, which is why the
-- family sits outside the corpus sweep and outside 'Lara.Mutate.mutationBases'.
module Lara.Mutate.Cycle
  ( cycleMutants
  ) where

import Lara.AST
import Lara.Prop (Prop (..), Term (..))
import Lara.Replay (CoreVersion (..), mkCheckInput, mkReplayId)
import Lara.Sigma (ConSig (..), PredSig (..), Sigma (..), Sort (..), SortName (..))
import Lara.Wire (encodeCheckInput, printSExpr)

import Lara.Mutate
  ( Expected (..)
  , Mutant (..)
  , MutationOp (..)
  )
import Lara.Mutate.Seed (streamFor)

-- | Attack N-cycles are the one Phase D mutation class that is specified NOT
-- to reject (spec §10.1): grounded semantics labels every cycle member
-- @undec@, so every queried claim is @contested@. Sizes are drawn from the
-- seeded stream; the units are constructed (they mutate no base anchor).
cycleMutants :: [Mutant]
cycleMutants =
  [ Mutant
      ("cycle-rebut-" ++ show n ++ ".sexp")
      "-"
      OpRebutCycle
      ExpectAllContested
      Nothing
      (cycleBytes n)
  | n <- sizes
  ]
  where
    draws = take 16 (streamFor "-" OpRebutCycle)
    sizes = takeDistinct 4 [2 + fromIntegral (w `mod` 8) | w <- draws]
    takeDistinct k = go []
      where
        go acc _ | length acc == k = reverse acc
        go acc [] = reverse acc
        go acc (x : xs)
          | x `elem` acc = go acc xs
          | otherwise = go (x : acc) xs

cycleBytes :: Int -> String
cycleBytes n = case checkInput of
  Right input -> printSExpr (encodeCheckInput input) ++ "\n"
  Left err -> error ("cycleBytes: impossible replay identity error: " ++ show err)
  where
    checkInput = do
      rid <-
        mkReplayId
          LaraCoreV02
          (PolicyId "mutation-cycles-v1")
          [(BackendId "nd", "1")]
          []
          (Digest "sha256:mutation-cycles-v1")
      mkCheckInput rid unit
    conName i = "c" ++ show i
    conTerm i = TCon (FunSym (conName i)) []
    holds i = Prop (Pred "holds") [conTerm i]
    obs i = Prop (Pred "obs") [conTerm i]
    holdsPat = AtomPat (Pred "holds") [PVar (Param "X")]
    obsPat = AtomPat (Pred "obs") [PVar (Param "X")]
    cyc = Rule (RuleId "cyc") [Param "X"] Defeasible [obsPat] [] holdsPat False [] []
    groundPat i = AtomPat (Pred "holds") [PLit (conTerm i)]
    contraries = [Contrary (groundPat i) (groundPat (succIx i)) | i <- ixes]
    leaves = [(LeafId ("l" ++ show i), obs i) | i <- ixes]
    args =
      [ ( ArgId ("a" ++ show i)
        , SRule
            (RuleId "cyc")
            [(Param "X", conTerm i)]
            [SLeaf (LeafId ("l" ++ show i))]
            []
            []
            AssuranceNone
        )
      | i <- ixes
      ]
    attacks = [Rebut (ArgId ("a" ++ show i)) (ArgId ("a" ++ show (succIx i))) | i <- ixes]
    queries = map holds ixes
    ixes = [0 .. n - 1]
    succIx i = (i + 1) `mod` n
    -- The synthetic unit's own generated Σ (§8): the operator that invents
    -- a vocabulary is the site that knows its sorts, so `mutation-cycles-v1`
    -- declares one opaque sort for its cycle nodes rather than tripping the new
    -- stage-2 check on incidental Σ noise.
    nodeSort = SortDecl (SortName "Node")
    sigma =
      Sigma
        { sigmaSorts = [SortName "Node"]
        , sigmaCons = [ConSig (FunSym (conName i)) [] nodeSort | i <- ixes]
        , sigmaPreds =
            [ PredSig (Pred "holds") [nodeSort]
            , PredSig (Pred "obs") [nodeSort]
            ]
        }
    unit =
      Unit
        sigma
        [cyc]
        contraries
        []
        []
        leaves
        args
        attacks
        queries
        []
        QuarantineOnConflict
