-- | The required v0.1 reference strict backend: intuitionistic natural
-- deduction for implication and falsum (@docs/strict-backend-decision.md@ §4.1;
-- spec §5).
--
-- This adapter is deliberately __modest__: it certifies only the propositional
-- consequences visible in its own encoding. Domain laws (arithmetic, temporal,
-- code behavior) are __not__ hidden axioms here — they remain explicit theory
-- dependencies or trusted policy rules. Keeping a real reference adapter (not
-- just the abstract seam) is what makes the backend interface concrete rather
-- than hypothetical.
--
-- == Formulas and certificates
--
-- > phi ::= a | false | phi -> phi                       -- backend formulas
-- > e   ::= hyp i | lam phi e | app e e | abort phi e     -- de Bruijn certificates
--
-- Certificates use __de Bruijn indices__, so binding and dependency checking
-- are syntactic. An index counts the enclosing @lam@ binders outward; an index
-- that overshoots the binders refers into the __free context__, which is the
-- source premises followed by the selected theory entries.
--
-- == Encoding and the obligations it discharges
--
-- > encode_ND(p) = atom(canonicalSerialize(nf p))
--
-- Here the canonical serialization is @'show' . 'nf'@ on the source
-- proposition. Derived 'Show' is injective on the 'Prop' AST, so
--
-- > p ≡ q   iff   nf p == nf q   iff   encodeND p == encodeND q,
--
-- which is exactly __normalization fidelity__ (decision doc §2 obligation 2):
-- the forward direction preserves source identity, the reverse prevents the
-- encoder from collapsing distinct propositions.
--
-- The type checker discharges the remaining obligations:
--
--   * __decidable replay__ (obligation 1) — 'inferType' is a total structural
--     recursion;
--   * __certificate soundness__ (obligation 3) — Theorem 4: a well-typed
--     certificate is Boolean-valid, proved by induction on the typing
--     derivation (the property suite exercises this by construction);
--   * __dependency accountability + exactness__ (obligation 4 / Lemma 5) — the
--     free de Bruijn indices of an accepted certificate are /exactly/ the
--     premise/theory slots its derivation depends on; 'inferType' returns that
--     set and the seam maps it to 'Dependency' values.
module Lara.Strict.ND
  ( -- * Backend formulas and certificates
    Formula (..)
  , Cert (..)
    -- * Encoding
  , encodeND
    -- * Type checking (the replay)
  , inferType
    -- * The registered adapter
  , ndBackendId
  , mkNDBackend
  ) where

import Data.Set (Set)
import qualified Data.Set as Set

import Lara.Prop (Prop, nf)
import Lara.Strict
  ( Backend (..)
  , BackendId (..)
  , Dependency (..)
  , SExpr (..)
  , TheoryDigest
  )

-- ---------------------------------------------------------------------------
-- Backend formulas and certificates
-- ---------------------------------------------------------------------------

-- | A backend formula. Atoms are the injective serialization of a normalized
-- source proposition (see 'encodeND'); the producer references a source
-- proposition by that same string.
data Formula
  = FAtom String
  | FFalse
  | FImp Formula Formula
  deriving (Eq, Ord, Show)

-- | A natural-deduction certificate in de Bruijn form.
data Cert
  = -- | @hyp i@: the assumption at de Bruijn index @i@
    Hyp Int
  | -- | @lam phi e@: implication introduction; @phi@ is the (annotated) antecedent
    Lam Formula Cert
  | -- | @app f x@: implication elimination
    App Cert Cert
  | -- | @abort phi e@: falsum elimination to @phi@; @e@ must conclude @false@
    Abort Formula Cert
  deriving (Eq, Ord, Show)

-- ---------------------------------------------------------------------------
-- Encoding
-- ---------------------------------------------------------------------------

-- | @encode_ND(p) = atom(canonicalSerialize(nf p))@. The serialization is
-- @'show' . 'nf'@, which is injective on the 'Prop' AST, discharging
-- normalization fidelity.
encodeND :: Prop -> Formula
encodeND = FAtom . show . nf

-- ---------------------------------------------------------------------------
-- Type checking (the replay)
-- ---------------------------------------------------------------------------

-- | Infer the formula of a certificate and the set of __free context slots__ it
-- depends on.
--
-- @'inferType' locals free e@ checks @e@ where @locals@ are the formulas bound
-- by enclosing @lam@s (innermost first) and @free@ is the fixed free context
-- (premise encodings followed by theory encodings). It returns the derived
-- formula and the set of indices /into @free@/ actually consulted — a locally
-- bound assumption contributes nothing (Lemma 5).
--
-- Total and deterministic: every constructor has one rule and every lookup is
-- range-checked, so it is a decidable replay (obligation 1).
inferType :: [Formula] -> [Formula] -> Cert -> Either String (Formula, Set Int)
inferType locals free = go locals
  where
    nFree = length free

    go :: [Formula] -> Cert -> Either String (Formula, Set Int)
    go ls (Hyp i)
      | i < 0 = Left ("negative de Bruijn index " ++ show i)
      | i < length ls = Right (ls !! i, Set.empty) -- locally bound: not a dependency
      | otherwise =
          let j = i - length ls -- into the free context
           in if j < nFree
                then Right (free !! j, Set.singleton j)
                else
                  Left
                    ( "free de Bruijn index out of range: hyp "
                        ++ show i
                        ++ " with "
                        ++ show (length ls)
                        ++ " binder(s) and "
                        ++ show nFree
                        ++ " free slot(s)"
                    )
    go ls (Lam phi e) = do
      (psi, deps) <- go (phi : ls) e
      Right (FImp phi psi, deps)
    go ls (App f x) = do
      (ft, fdeps) <- go ls f
      (xt, xdeps) <- go ls x
      case ft of
        FImp a b
          | a == xt -> Right (b, Set.union fdeps xdeps)
          | otherwise ->
              Left ("application mismatch: expected " ++ show a ++ ", got " ++ show xt)
        other -> Left ("application of a non-implication: " ++ show other)
    go ls (Abort phi e) = do
      (et, deps) <- go ls e
      case et of
        FFalse -> Right (phi, deps)
        other -> Left ("abort of a non-false proof: " ++ show other)

-- ---------------------------------------------------------------------------
-- SExpr wire decoding (the closed decoder)
-- ---------------------------------------------------------------------------

-- The certificate reaches the adapter as an opaque 'SExpr'; only this module
-- decodes it (closed registration). Wire grammar:
--
-- > formula := (atom STRING) | false | (imp FORMULA FORMULA)
-- > cert    := (hyp N) | (lam FORMULA CERT) | (app CERT CERT) | (abort FORMULA CERT)

decodeFormula :: SExpr -> Either String Formula
decodeFormula (SAtom "false") = Right FFalse
decodeFormula (SList [SAtom "atom", SAtom s]) = Right (FAtom s)
decodeFormula (SList [SAtom "imp", a, b]) = FImp <$> decodeFormula a <*> decodeFormula b
decodeFormula e = Left ("malformed ND formula: " ++ show e)

decodeCert :: SExpr -> Either String Cert
decodeCert (SList [SAtom "hyp", SAtom n]) =
  case reads n of
    [(i, "")] -> Right (Hyp i)
    _ -> Left ("malformed de Bruijn index: " ++ show n)
decodeCert (SList [SAtom "lam", phi, e]) = Lam <$> decodeFormula phi <*> decodeCert e
decodeCert (SList [SAtom "app", f, x]) = App <$> decodeCert f <*> decodeCert x
decodeCert (SList [SAtom "abort", phi, e]) = Abort <$> decodeFormula phi <*> decodeCert e
decodeCert e = Left ("malformed ND certificate: " ++ show e)

-- ---------------------------------------------------------------------------
-- The registered adapter
-- ---------------------------------------------------------------------------

-- | The reference natural-deduction backend identifier: @nd\@1@.
ndBackendId :: BackendId
ndBackendId = BackendId {backendName = "nd", backendVersion = 1}

-- | Build the reference adapter with a __fixed__ theory table mapping each
-- admissible 'TheoryDigest' to its finite list of source propositions (the
-- theory entries, encoded on demand). Closed registration: the table is fixed
-- at construction; an artifact selects a digest but cannot change or extend it.
--
-- On a strict step the adapter encodes the premises and goal, resolves the
-- theory digest to its entry encodings, decodes and replays the certificate,
-- checks that it concludes @encode_ND(goal)@, and returns the consulted
-- 'Dependency' set: a free slot below @length premises@ is a 'PremiseSlot', at
-- or above it a 'TheoryEntry'.
mkNDBackend :: [(TheoryDigest, [Prop])] -> Backend
mkNDBackend theories =
  Backend
    { backendId = ndBackendId
    , runBackend = run
    }
  where
    run :: TheoryDigest -> [Prop] -> Prop -> SExpr -> Either String (Set Dependency)
    run digest premises goal certSExpr =
      case lookup digest theories of
        Nothing -> Left ("unknown theory digest: " ++ show digest)
        Just theoryProps -> do
          cert <- decodeCert certSExpr
          let nPrem = length premises
              free = map encodeND premises ++ map encodeND theoryProps
          (concl, slots) <- inferType [] free cert
          let goalF = encodeND goal
          if concl == goalF
            then Right (Set.map (toDependency nPrem) slots)
            else
              Left
                ( "certificate concludes "
                    ++ show concl
                    ++ " but the goal encodes to "
                    ++ show goalF
                )

    toDependency :: Int -> Int -> Dependency
    toDependency nPrem slot
      | slot < nPrem = PremiseSlot slot
      | otherwise = TheoryEntry (slot - nPrem)
