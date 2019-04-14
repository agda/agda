-- | Logically consistent comparison of floating point numbers.
module Agda.Utils.Float where

import Numeric.IEEE ( IEEE(identicalIEEE) )

floatEq :: Double -> Double -> Bool
floatEq x y = identicalIEEE x y || (isNaN x && isNaN y)

floatLt :: Double -> Double -> Bool
floatLt x y =
  case compareFloat x y of
    LT -> True
    _  -> False
  where
    -- Also implemented in the GHC backend
    compareFloat :: Double -> Double -> Ordering
    compareFloat x y
      | identicalIEEE x y          = EQ
      | isNegInf x                 = LT
      | isNegInf y                 = GT
      | isNaN x && isNaN y         = EQ
      | isNaN x                    = LT
      | isNaN y                    = GT
      | otherwise                  = compare (x, isNegZero y) (y, isNegZero x)
    isNegInf  z = z < 0 && isInfinite z
    isNegZero z = identicalIEEE z (-0.0)
