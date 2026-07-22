-- | Property tests for 'Lara.Prop' — the algebraic laws @≡@ must satisfy to be
-- a trusted-base equality (spec §3.2, result 11).
--
-- These cover the carve-out layer 1 obligations: @≡@ is an equivalence
-- relation, is exactly @nf@-equality, is stable under 'nf' (idempotence), and
-- respects the /no argument reordering/ rule (@p(a,b) ≢ p(b,a)@ for distinct
-- @a,b@). Literal canonicalization ('canonNum') is checked separately.
module PropSpec (propSpecProps) where

import Test.QuickCheck

import Lara.Prop
  ( FunSym (..)
  , Prop (..)
  , Pred (..)
  , Term (..)
  , canonNum
  , equiv
  , nf
  )

-- ---------------------------------------------------------------------------
-- Generators
-- ---------------------------------------------------------------------------

genIdent :: Gen String
genIdent = (: []) <$> elements ['a' .. 'e']

-- | A numeric literal with cosmetic noise (sign, leading/trailing zeros) so
-- that generated values exercise 'canonNum'.
genNoisyNum :: Gen String
genNoisyNum = do
  sign <- elements ["", "+", "-"]
  lead <- listOf (pure '0')
  digits <- listOf1 (elements ['0' .. '9'])
  frac <- oneof [pure "", ('.' :) <$> listOf (elements ['0' .. '9'])]
  pure (sign ++ lead ++ digits ++ frac)

genTerm :: Gen Term
genTerm = sized go
  where
    go n
      | n <= 0 =
          oneof
            [ TNum <$> genNoisyNum
            , TStr <$> listOf (elements ['a' .. 'c'])
            , TCon <$> (FunSym <$> genIdent) <*> pure []
            ]
      | otherwise =
          frequency
            [ (3, go 0)
            , (1, TCon <$> (FunSym <$> genIdent) <*> resize (n `div` 2) (listOf (go (n `div` 2))))
            ]

genProp :: Gen Prop
genProp = Prop <$> (Pred <$> genIdent) <*> sized (\n -> resize n (listOf (resize n genTerm)))

newtype P = P Prop deriving (Show)

instance Arbitrary P where
  arbitrary = P <$> genProp

-- ---------------------------------------------------------------------------
-- Properties
-- ---------------------------------------------------------------------------

-- | Reflexivity: @p ≡ p@.
prop_reflexive :: P -> Bool
prop_reflexive (P p) = equiv p p

-- | Symmetry: @p ≡ q  <=>  q ≡ p@.
prop_symmetric :: P -> P -> Bool
prop_symmetric (P p) (P q) = equiv p q == equiv q p

-- | Transitivity. We seed the middle term by canonicalization so that
-- nontrivial (True) instances actually occur, not just vacuous ones.
prop_transitive :: P -> P -> Bool
prop_transitive (P p) (P r) =
  let q = nf p -- p ≡ q by construction
   in not (equiv p q && equiv q r) || equiv p r

-- | @≡@ is exactly @nf@-equality.
prop_isNfEquality :: P -> P -> Bool
prop_isNfEquality (P p) (P q) = equiv p q == (nf p == nf q)

-- | Idempotence of the normal form: @nf (nf p) = nf p@.
prop_nfIdempotent :: P -> Bool
prop_nfIdempotent (P p) = nf (nf p) == nf p

-- | No argument reordering: for distinct normalized arguments, swapping them
-- breaks identity. @p(a,b) ≢ p(b,a)@ unless @a ≡ b@.
prop_noReorder :: Property
prop_noReorder =
  forAll genTerm $ \a ->
    forAll genTerm $ \b ->
      (nf (Prop (Pred "p") [a, b]) /= nf (Prop (Pred "p") [b, a])) == (nfArg a /= nfArg b)
  where
    -- a term's normal form as it appears inside a Prop
    nfArg t = let Prop _ [t'] = nf (Prop (Pred "p") [t]) in t'

-- | 'canonNum' identifies surface variants of the same value.
prop_canonNumVariants :: Bool
prop_canonNumVariants =
  and
    [ canonNum "+2.1" == "2.1"
    , canonNum "2.10" == "2.1"
    , canonNum "02.100" == "2.1"
    , canonNum "-0.0" == "0"
    , canonNum "+0" == "0"
    , canonNum "003" == "3"
    , canonNum "1." == "1"
    ]

-- | 'canonNum' is idempotent.
prop_canonNumIdempotent :: Property
prop_canonNumIdempotent =
  forAll genNoisyNum $ \s -> canonNum (canonNum s) == canonNum s

-- ---------------------------------------------------------------------------
-- Exported runner
-- ---------------------------------------------------------------------------

-- | Named QuickCheck actions for the 'Lara.Prop' layer, run by the main suite.
propSpecProps :: [(String, IO Result)]
propSpecProps =
  [ ("prop ≡ reflexive", quickCheckResult prop_reflexive)
  , ("prop ≡ symmetric", quickCheckResult prop_symmetric)
  , ("prop ≡ transitive", quickCheckResult prop_transitive)
  , ("prop ≡ is nf-equality", quickCheckResult prop_isNfEquality)
  , ("prop nf idempotent", quickCheckResult prop_nfIdempotent)
  , ("prop no argument reordering", quickCheckResult prop_noReorder)
  , ("canonNum variants collapse", quickCheckResult prop_canonNumVariants)
  , ("canonNum idempotent", quickCheckResult prop_canonNumIdempotent)
  ]
