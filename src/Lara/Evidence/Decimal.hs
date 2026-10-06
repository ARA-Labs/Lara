module Lara.Evidence.Decimal (decimalTerm) where

import Data.Ratio ((%))
import Lara.Prop (Term (..))
import Lara.Strict.Cell (renderDecimal)

decimalTerm :: String -> Either String Term
decimalTerm input = do
  let (negative, unsigned) = case input of
        '-':s -> (True,s)
        '+':s -> (False,s)
        s -> (False,s)
      (mantissa,exponentPart) = break (`elem` "eE") unsigned
      (whole,fractionPart) = break (== '.') mantissa
      fraction = case fractionPart of '.':s -> s; _ -> ""
      digits s = not (null s) && all (`elem` ['0'..'9']) s
  if not (digits whole) || (not (null fractionPart) && not (digits fraction))
    then Left "invalid decimal grammar" else Right ()
  if length whole + length fraction > 256 then Left "decimal mantissa bound exceeded" else Right ()
  exponent <- case exponentPart of
    [] -> Right (0 :: Int)
    _:raw -> let (sgn,ds) = case raw of '-':s -> (-1,s); '+':s -> (1,s); s -> (1,s)
             in if not (digits ds) then Left "invalid decimal exponent"
                else if length ds > 3 then Left "decimal exponent bound exceeded"
                else let e = sgn * read ds in if abs e > 256 then Left "decimal exponent bound exceeded" else Right e
  let coefficient = read (whole ++ fraction) :: Integer
      scale = length fraction - exponent
      signed = if negative then negate coefficient else coefficient
      value = if scale >= 0 then signed % (10 ^ scale) else fromInteger (signed * 10 ^ negate scale)
  pure (TNum (renderDecimal value))
