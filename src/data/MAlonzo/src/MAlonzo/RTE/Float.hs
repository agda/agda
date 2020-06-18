{-# LANGUAGE CPP       #-}
{-# LANGUAGE PolyKinds #-}

module MAlonzo.RTE.Float where

import Numeric.IEEE ( IEEE(identicalIEEE, nan) )
#if __GLASGOW_HASKELL__ >= 804
import GHC.Float (castDoubleToWord64)
#else
import System.IO.Unsafe (unsafePerformIO)
import qualified Foreign          as F
import qualified Foreign.Storable as F
#endif

eqFloat :: Double -> Double -> Bool
eqFloat x y = identicalIEEE x y || (isNaN x && isNaN y)

eqNumFloat :: Double -> Double -> Bool
eqNumFloat = (==)

ltNumFloat :: Double -> Double -> Bool
ltNumFloat = (<)

negativeZero :: Double
negativeZero = -0.0

positiveInfinity :: Double
positiveInfinity = 1.0 / 0.0

negativeInfinity :: Double
negativeInfinity = -positiveInfinity

positiveNaN :: Double
positiveNaN = 0.0 / 0.0

negativeNaN :: Double
negativeNaN = -positiveNaN

-- Adapted from the same function on Agda.Syntax.Literal.
compareFloat :: Double -> Double -> Ordering
compareFloat x y
  | identicalIEEE x y          = EQ
  | isNegInf x                 = LT
  | isNegInf y                 = GT
  | isNaN x && isNaN y         = EQ
  | isNaN x                    = LT
  | isNaN y                    = GT
  | otherwise                  = compare (x, isNegZero y) (y, isNegZero x)
  where
    isNegInf  z = z < 0 && isInfinite z
    isNegZero z = identicalIEEE z negativeZero

ltFloat :: Double -> Double -> Bool
ltFloat x y = case compareFloat x y of
                LT -> True
                _  -> False

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

