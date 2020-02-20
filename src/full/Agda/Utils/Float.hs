{-# LANGUAGE CPP #-}

-- | Logically consistent comparison of floating point numbers.
module Agda.Utils.Float
  ( normaliseNaN
  , doubleToWord64
  , floatEq
  , floatLt
  , toStringWithoutDotZero
  ) where

import Data.Maybe       ( fromMaybe )
import Data.Word
import Numeric.IEEE     ( IEEE(identicalIEEE, nan) )
#if __GLASGOW_HASKELL__ >= 804
import GHC.Float        ( castDoubleToWord64 )
#else
import System.IO.Unsafe ( unsafePerformIO )
import qualified Foreign as F
#endif

import Agda.Utils.List  ( stripSuffix )

#if __GLASGOW_HASKELL__ < 804
castDoubleToWord64 :: Double -> Word64
castDoubleToWord64 float = unsafePerformIO $ F.alloca $ \buf -> do
  F.poke (F.castPtr buf) float
  F.peek buf
#endif

normaliseNaN :: Double -> Double
normaliseNaN x
  | isNaN x   = nan
  | otherwise = x

doubleToWord64 :: Double -> Word64
doubleToWord64 = castDoubleToWord64 . normaliseNaN

floatEq :: Double -> Double -> Bool
floatEq x y = identicalIEEE x y  || (isNaN x && isNaN y)

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

-- | Remove suffix @.0@ from printed floating point number.
toStringWithoutDotZero :: Double -> String
toStringWithoutDotZero d = fromMaybe s $ stripSuffix ".0" s
  where s = show d
