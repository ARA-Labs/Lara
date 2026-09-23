-- | The many-sorted proposition signature @Σ@ (spec §2, §3.4) and ground
-- sorting — the object rejection class __R2__ is about.
--
-- v0.1 carried @Σ@ as an elaborator-private @[(Pred, Int)]@ that nothing read.
-- @lara-core\@0.2@ makes it a declared, wire-carried field of the checker
-- 'Lara.AST.Unit' and a checked precondition of reading the policy as patterns
-- ("Lara.Check" stage 2). This module owns the object and the /ground/ half of
-- the judgment:
--
--   * 'Sort' — two built-in base sorts ('SortNum', 'SortStr': the sorts of
--     'TNum' and 'TStr') plus opaque declared sorts. No subtyping, no sort
--     variables, no sort constructors; sort equality is name equality.
--   * 'Sigma' — declared sorts, a constructor table ('ConSig': argument sorts
--     and a result sort) and a predicate table ('PredSig': argument sorts).
--     Arity is /subsumed/, not replaced: it is the length of the argument-sort
--     vector, so the old @[(Pred, Int)]@ is @map (\\s -> (predSym s, length
--     (predArgs s)))@ and the new object is strictly stronger on every axis.
--   * 'sigmaFault' — Σ well-formedness: no duplicate declaration, no
--     declaration shadowing a base-sort name, no signature naming an undeclared
--     sort.
--   * 'sortOf' \/ 'sortCheckProp' — the ground judgment, total except on
--     undeclared symbols.
--
-- The /pattern/ half — rule patterns under derived parameter sorts, contraries,
-- exceptions, θ ranges, and the whole-'Lara.AST.Unit' stage — lives in
-- "Lara.Sigma.WellSorted", which is the same deliverable split at the one place
-- the module graph forces: 'Lara.AST.Unit' carries a 'Sigma', so this module
-- cannot see "Lara.AST".
--
-- Mirrors @lean\/Lara\/Sigma.lean@.
module Lara.Sigma
  ( -- * Sorts
    SortName (..)
  , Sort (..)
  , baseSortTable
  , baseSortNames
  , sortFromText
  , sortText
    -- * The signature
  , ConSig (..)
  , PredSig (..)
  , Sigma (..)
  , emptySigma
  , lookupCon
  , lookupPred
  , predArities
    -- * Σ-aware generation
  , declarePred
  , declarePredFor
  , declareCon
  , sigmaOf
    -- * Σ well-formedness
  , SigmaFault (..)
  , sigmaFault
  , sigmaWellFormed
    -- * Ground sorting
  , SortFault (..)
  , sortOf
  , sortCheckTerm
  , sortCheckProp
  ) where

import Data.List (find)

import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))

-- ---------------------------------------------------------------------------
-- Sorts
-- ---------------------------------------------------------------------------

-- | A declared sort name (@System@, @Cell@, …). Its own newtype because the
-- sort namespace is disjoint from every identifier namespace in "Lara.AST": a
-- sort is not a predicate, a constructor, or a measurand.
newtype SortName = SortName String
  deriving (Eq, Ord, Show)

-- | A sort. The two base sorts are built in and not declarable: they are the
-- sorts of the two 'Term' literal constructors, so a signature that could
-- redefine them could make 'sortOf' non-total on ground data the frontend never
-- declared.
data Sort
  = -- | the sort of every 'TNum'
    SortNum
  | -- | the sort of every 'TStr'
    SortStr
  | -- | a declared, opaque sort
    SortDecl SortName
  deriving (Eq, Ord, Show)

-- | The reserved base-sort vocabulary. This is the only table containing the
-- concrete spellings; parsing, printing, and shadow checks all derive from it.
baseSortTable :: [(String, Sort)]
baseSortTable = [("Num", SortNum), ("Str", SortStr)]

-- | The reserved base-sort spellings. A @sort@ declaration using either is a
-- Σ-well-formedness reject ('SFShadowsBase') rather than a silent shadow.
baseSortNames :: [String]
baseSortNames = map fst baseSortTable

-- | Parse a sort reference. Non-base spellings denote declared opaque sorts.
sortFromText :: String -> Sort
sortFromText n = maybe (SortDecl (SortName n)) id (lookup n baseSortTable)

-- | The canonical surface spelling of a sort.
sortText :: Sort -> String
sortText (SortDecl (SortName n)) = n
sortText s =
  case find ((== s) . snd) baseSortTable of
    Just (n, _) -> n
    Nothing -> error "Lara.Sigma.sortText: missing base-sort table entry"

-- ---------------------------------------------------------------------------
-- The signature
-- ---------------------------------------------------------------------------

-- | A constructor (function-symbol) signature: @con k(s1, …, sn) : s@. A
-- nullary constant is @'ConSig' k [] s@ — the dominant population in a real
-- corpus, since every bare identifier argument is a @'TCon' k []@.
data ConSig = ConSig
  { conSym :: FunSym
  , conArgs :: [Sort]
  , conResult :: Sort
  }
  deriving (Eq, Show)

-- | A predicate signature: @pred p(s1, …, sn)@. Predicates have no result sort
-- — a 'Prop' is not a term — which is exactly why they are a separate table.
data PredSig = PredSig
  { predSym :: Pred
  , predArgs :: [Sort]
  }
  deriving (Eq, Show)

-- | A first-order many-sorted signature: declared sorts plus separate
-- constructor and predicate tables (spec §2's "separate arity tables for
-- predicates and function symbols", now carrying sorts).
--
-- Declaration order is retained so the wire encoding and the surface printer
-- are canonical.
data Sigma = Sigma
  { sigmaSorts :: [SortName]
  , sigmaCons :: [ConSig]
  , sigmaPreds :: [PredSig]
  }
  deriving (Eq, Show)

-- | The signature declaring nothing. Under strict mode (decision 2) every
-- symbol is undeclared against it, so it accepts only symbol-free units; it is
-- the unit of the object, not a permissive default.
emptySigma :: Sigma
emptySigma = Sigma [] [] []

lookupCon :: Sigma -> FunSym -> Maybe ConSig
lookupCon sg k = find ((== k) . conSym) (sigmaCons sg)

lookupPred :: Sigma -> Pred -> Maybe PredSig
lookupPred sg p = find ((== p) . predSym) (sigmaPreds sg)

-- | The v0.1 @[(Pred, Int)]@ view, recovered by forgetting sorts. Kept as the
-- explicit witness that the new object subsumes the old one.
predArities :: Sigma -> [(Pred, Int)]
predArities sg = [(predSym s, length (predArgs s)) | s <- sigmaPreds sg]

-- ---------------------------------------------------------------------------
-- Σ-aware generation
-- ---------------------------------------------------------------------------
--
-- The mutation generators inject fresh symbols (§8). Σ travels per unit and
-- the operator that injects a symbol is exactly the site that knows its
-- argument sorts, so each such operator extends the mutant's carried Σ here.
-- Without this a symbol-injecting operator would flip its mutant to R2 and
-- silently stop testing the class it seeds.

-- | Append a predicate signature. Idempotent on an already-declared symbol, so
-- an operator that fires twice on one unit does not produce a duplicate
-- declaration (itself a Σ-well-formedness reject).
declarePred :: Pred -> [Sort] -> Sigma -> Sigma
declarePred p ss sg
  | any ((== p) . predSym) (sigmaPreds sg) = sg
  | otherwise = sg{sigmaPreds = sigmaPreds sg ++ [PredSig p ss]}

-- | Declare a fresh predicate whose argument sorts are read off the ground
-- terms it will be applied to. This is the common case: an injected atom reuses
-- an existing atom's arguments, so its signature is /derivable/ and does not
-- have to be guessed.
--
-- A term that is not well-sorted under @sg@ contributes 'SortStr'. That is
-- unreachable on a well-sorted base unit, and if it ever were reached the
-- generator's own verification pass would abort on the resulting R2 rather than
-- writing a wrong mutant.
declarePredFor :: [Term] -> Pred -> Sigma -> Sigma
declarePredFor ts p sg =
  declarePred p [either (const SortStr) id (sortOf sg t) | t <- ts] sg

-- | Append a constructor signature, idempotent as 'declarePred'.
declareCon :: FunSym -> [Sort] -> Sort -> Sigma -> Sigma
declareCon k ss res sg
  | any ((== k) . conSym) (sigmaCons sg) = sg
  | otherwise = sg{sigmaCons = sigmaCons sg ++ [ConSig k ss res]}

-- | Compact authored-signature builder: declared sorts, constructors as
-- @(symbol, argument sorts, result sort)@, and predicates as
-- @(symbol, argument sorts)@.
sigmaOf :: [String] -> [(String, [String], String)] -> [(String, [String])] -> Sigma
sigmaOf sorts cons preds =
  Sigma
    (map SortName sorts)
    [ConSig (FunSym k) (map sortFromText args) (sortFromText result) | (k, args, result) <- cons]
    [PredSig (Pred p) (map sortFromText args) | (p, args) <- preds]

-- ---------------------------------------------------------------------------
-- Σ well-formedness
-- ---------------------------------------------------------------------------

-- | A malformed signature. Declaration-order first fault; each arm names the
-- offending declaration.
data SigmaFault
  = -- | the same sort declared twice
    SFDuplicateSort SortName
  | -- | @sort Num@ \/ @sort Str@: a declaration shadowing a base sort
    SFShadowsBase SortName
  | -- | the same constructor declared twice
    SFDuplicateCon FunSym
  | -- | the same predicate declared twice
    SFDuplicatePred Pred
  | -- | a constructor signature naming an undeclared sort
    SFConUndeclaredSort FunSym SortName
  | -- | a predicate signature naming an undeclared sort
    SFPredUndeclaredSort Pred SortName
  deriving (Eq, Show)

-- | The first Σ-well-formedness fault in declaration order, or 'Nothing'.
--
-- Order: sorts (shadowing before duplication, per declaration), then
-- constructors, then predicates — so the diagnostic is deterministic and both
-- runtimes report the same one.
sigmaFault :: Sigma -> Maybe SigmaFault
sigmaFault sg =
  firstJust
    [ scanSorts [] (sigmaSorts sg)
    , scanCons [] (sigmaCons sg)
    , scanPreds [] (sigmaPreds sg)
    ]
  where
    declared = sigmaSorts sg

    scanSorts _ [] = Nothing
    scanSorts seen (n@(SortName raw) : rest)
      | raw `elem` baseSortNames = Just (SFShadowsBase n)
      | n `elem` seen = Just (SFDuplicateSort n)
      | otherwise = scanSorts (n : seen) rest

    scanCons _ [] = Nothing
    scanCons seen (c : rest)
      | conSym c `elem` seen = Just (SFDuplicateCon (conSym c))
      | otherwise = case firstUndeclared declared (conArgs c ++ [conResult c]) of
          Just n -> Just (SFConUndeclaredSort (conSym c) n)
          Nothing -> scanCons (conSym c : seen) rest

    scanPreds _ [] = Nothing
    scanPreds seen (p : rest)
      | predSym p `elem` seen = Just (SFDuplicatePred (predSym p))
      | otherwise = case firstUndeclared declared (predArgs p) of
          Just n -> Just (SFPredUndeclaredSort (predSym p) n)
          Nothing -> scanPreds (predSym p : seen) rest

-- | Decidable Σ well-formedness, derived from the located scan.
sigmaWellFormed :: Sigma -> Bool
sigmaWellFormed sg = case sigmaFault sg of
  Nothing -> True
  Just _ -> False

firstUndeclared :: [SortName] -> [Sort] -> Maybe SortName
firstUndeclared declared = go
  where
    go [] = Nothing
    go (SortDecl n : rest)
      | n `notElem` declared = Just n
      | otherwise = go rest
    go (_ : rest) = go rest

firstJust :: [Maybe a] -> Maybe a
firstJust = foldr (\m acc -> maybe acc Just m) Nothing

-- ---------------------------------------------------------------------------
-- Ground sorting
-- ---------------------------------------------------------------------------

-- | Why a term or atom is not well-sorted. Retains the offending symbol and
-- the sorts involved; the public located diagnostic reports R2 at the policy.
data SortFault
  = -- | a predicate head with no @pred@ declaration
    FaultUndeclaredPred Pred
  | -- | a constructor head with no @con@ declaration
    FaultUndeclaredCon FunSym
  | -- | @pred p@ declared with the first arity, applied at the second
    FaultPredArity Pred Int Int
  | -- | @con k@ declared with the first arity, applied at the second
    FaultConArity FunSym Int Int
  | -- | an argument of the expected sort (first) supplied at the actual one
    FaultArgSort Sort Sort
  deriving (Eq, Show)

-- | The sort of a ground term under @Σ@ (spec §3.4):
--
-- > sortOf(TNum _)   = Num
-- > sortOf(TStr _)   = Str
-- > sortOf(TCon k ts) = result sort of k, provided |ts| matches k's arity and
-- >                     each sortOf(t_i) equals k's declared i-th argument sort
--
-- Total except on undeclared symbols, arity mismatch, and argument-sort
-- mismatch — the three ground clauses of the amended R2.
sortOf :: Sigma -> Term -> Either SortFault Sort
sortOf _ (TNum _) = Right SortNum
sortOf _ (TStr _) = Right SortStr
sortOf sg (TCon k ts) = case lookupCon sg k of
  Nothing -> Left (FaultUndeclaredCon k)
  Just sig
    | length ts /= length (conArgs sig) ->
        Left (FaultConArity k (length (conArgs sig)) (length ts))
    | otherwise -> do
        mapM_ (uncurry (expectTerm sg)) (zip (conArgs sig) ts)
        Right (conResult sig)

-- | Check a ground term against an expected sort.
expectTerm :: Sigma -> Sort -> Term -> Either SortFault ()
expectTerm sg expected t = do
  actual <- sortOf sg t
  if actual == expected
    then Right ()
    else Left (FaultArgSort expected actual)

-- | 'sortOf' as a check, discarding the sort.
sortCheckTerm :: Sigma -> Term -> Maybe SortFault
sortCheckTerm sg t = case sortOf sg t of
  Left f -> Just f
  Right _ -> Nothing

-- | Well-sortedness of a ground atom: the head is declared, the arity matches,
-- and every argument has the declared sort. Left-to-right, first fault wins.
sortCheckProp :: Sigma -> Prop -> Maybe SortFault
sortCheckProp sg (Prop p ts) = case lookupPred sg p of
  Nothing -> Just (FaultUndeclaredPred p)
  Just sig
    | length ts /= length (predArgs sig) ->
        Just (FaultPredArity p (length (predArgs sig)) (length ts))
    | otherwise -> case mapM_ (uncurry (expectTerm sg)) (zip (predArgs sig) ts) of
        Left f -> Just f
        Right () -> Nothing
