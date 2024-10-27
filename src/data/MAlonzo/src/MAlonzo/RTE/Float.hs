{-# LANGUAGE CPP #-}

module MAlonzo.RTE.Float where

import Prelude
  ( Bool, Double, Int, Integer, Maybe(..), Ordering(..)
  , Eq(..), Ord(..), Functor(..)
  , Floating(..), Fractional(..), Integral(..), Num(..), Real(..), RealFloat(..), RealFrac(..)
  , ($), (.), otherwise, uncurry, undefined
  , (&&), fst, snd
  , (^), even, fromIntegral
  )

import Data.Bifunctor   ( bimap, second )
import Data.Function    ( on )
import Data.Maybe       ( fromMaybe )
import Data.Ratio       ( (%), numerator, denominator )
import Data.Word        ( Word64 )

#if __GLASGOW_HASKELL__ >= 804
import GHC.Float (castDoubleToWord64, castWord64ToDouble)
#else
import System.IO.Unsafe (unsafePerformIO)
import qualified Foreign          as F
import qualified Foreign.Storable as F
#endif

#if __GLASGOW_HASKELL__ < 804
castDoubleToWord64 :: Double -> Word64
castDoubleToWord64 float = unsafePerformIO $ F.alloca $ \buf -> do
  F.poke (F.castPtr buf) float
  F.peek buf

castWord64ToDouble :: Word64 -> Double
castWord64ToDouble word = unsafePerformIO $ F.alloca $ \buf -> do
  F.poke (F.castPtr buf) word
  F.peek buf
#endif

{-# INLINE doubleEq #-}
doubleEq :: Double -> Double -> Bool
doubleEq = (==)

{-# INLINE doubleLe #-}
doubleLe :: Double -> Double -> Bool
doubleLe = (<=)

{-# INLINE doubleLt #-}
doubleLt :: Double -> Double -> Bool
doubleLt = (<)

truncateDouble :: Double -> Double
truncateDouble = castWord64ToDouble . castDoubleToWord64

{-# INLINE intToDouble #-}
intToDouble :: Integral a => a -> Double
intToDouble = truncateDouble . fromIntegral

{-# INLINE doublePlus #-}
doublePlus :: Double -> Double -> Double
doublePlus x y = truncateDouble (x + y)

{-# INLINE doubleMinus #-}
doubleMinus :: Double -> Double -> Double
doubleMinus x y = truncateDouble (x - y)

{-# INLINE doubleTimes #-}
doubleTimes :: Double -> Double -> Double
doubleTimes x y = truncateDouble (x * y)

{-# INLINE doubleNegate #-}
doubleNegate :: Double -> Double
doubleNegate = negate -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleDiv #-}
doubleDiv :: Double -> Double -> Double
doubleDiv = (/) -- NOTE: doesn't cause underflow/overflow

{-# INLINE doublePow #-}
doublePow :: Double -> Double -> Double
doublePow x y = truncateDouble (x ** y)

{-# INLINE doubleSqrt #-}
doubleSqrt :: Double -> Double
doubleSqrt = sqrt -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleExp #-}
doubleExp :: Double -> Double
doubleExp x = truncateDouble (exp x)

{-# INLINE doubleLog #-}
doubleLog :: Double -> Double
doubleLog = log -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleSin #-}
doubleSin :: Double -> Double
doubleSin = sin -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleCos #-}
doubleCos :: Double -> Double
doubleCos = cos -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleTan #-}
doubleTan :: Double -> Double
doubleTan = tan -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleASin #-}
doubleASin :: Double -> Double
doubleASin = asin -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleACos #-}
doubleACos :: Double -> Double
doubleACos = acos -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleATan #-}
doubleATan :: Double -> Double
doubleATan = atan -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleATan2 #-}
doubleATan2 :: Double -> Double -> Double
doubleATan2 = atan2 -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleSinh #-}
doubleSinh :: Double -> Double
doubleSinh = sinh -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleCosh #-}
doubleCosh :: Double -> Double
doubleCosh = cosh -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleTanh #-}
doubleTanh :: Double -> Double
doubleTanh = tanh -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleASinh #-}
doubleASinh :: Double -> Double
doubleASinh = asinh -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleACosh #-}
doubleACosh :: Double -> Double
doubleACosh = acosh -- NOTE: doesn't cause underflow/overflow

{-# INLINE doubleATanh #-}
doubleATanh :: Double -> Double
doubleATanh = atanh -- NOTE: doesn't cause underflow/overflow

{-# INLINE negativeZero #-}
negativeZero :: Double
negativeZero = -0.0

positiveInfinity :: Double
positiveInfinity = 1.0 / 0.0

negativeInfinity :: Double
negativeInfinity = -positiveInfinity

nan :: Double
nan = 0.0 / 0.0

isPosInf :: Double -> Bool
isPosInf x = x > 0.0 && isInfinite x

isNegInf :: Double -> Bool
isNegInf x = x < 0.0 && isInfinite x

isPosZero :: Double -> Bool
isPosZero x = doubleDenotEq x 0.0

isNegZero :: Double -> Bool
isNegZero x = doubleDenotEq x (-0.0)

doubleRound :: Double -> Maybe Integer
doubleRound = fmap round . asFinite

doubleFloor :: Double -> Maybe Integer
doubleFloor = fmap floor . asFinite

doubleCeiling :: Double -> Maybe Integer
doubleCeiling = fmap ceiling . asFinite

normaliseNaN :: Double -> Double
normaliseNaN x
  | isNaN x   = nan
  | otherwise = x

doubleToWord64 :: Double -> Maybe Word64
doubleToWord64 x
  | isNaN x   = Nothing
  | otherwise = Just (castDoubleToWord64 x)

-- |Denotational equality for floating point numbers, checks bitwise equality.
--
--  NOTE: Denotational equality distinguishes NaNs, so its results may vary
--        depending on the architecture and compilation flags. Unfortunately,
--        this is a problem with floating-point numbers in general.
--
doubleDenotEq :: Double -> Double -> Bool
doubleDenotEq = (==) `on` doubleToWord64

-- |I guess "denotational orderings" are now a thing? The point is that we need
--  an Ord instance which provides a total ordering, and is consistent with the
--  denotational equality.
--
--  NOTE: The ordering induced via `doubleToWord64` is total, and is consistent
--        with `doubleDenotEq`. However, it is *deeply* unintuitive. For one, it
--        considers all negative numbers to be larger than positive numbers.
--
doubleDenotOrd :: Double -> Double -> Ordering
doubleDenotOrd = compare `on` doubleToWord64

-- |Return Just x if it's a finite number, otherwise return Nothing.
asFinite :: Double -> Maybe Double
asFinite x
  | isNaN      x = Nothing
  | isInfinite x = Nothing
  | otherwise    = Just x

-- |Decode a Double to an integer ratio.
doubleToRatio :: Double -> (Integer, Integer)
doubleToRatio x
  | isNaN      x = (0, 0)
  | isInfinite x = (signum (floor x), 0)
  | otherwise    = let r = toRational x in (numerator r, denominator r)

-- |Encode an integer ratio as a double.
ratioToDouble :: Integer -> Integer -> Double
ratioToDouble n d
  | d == 0 = case compare n 0 of
      LT -> negativeInfinity
      EQ -> nan
      GT -> positiveInfinity
  | otherwise = fromRational (n % d)

-- |Decode a Double to its mantissa and its exponent, normalised such that the
--  mantissa is the smallest possible number without loss of accuracy.
doubleDecode :: Double -> Maybe (Integer, Integer)
doubleDecode x
  | isNaN      x = Nothing
  | isInfinite x = Nothing
  | otherwise    = Just (uncurry normalise (second toInteger (decodeFloat x)))
  where
    normalise :: Integer -> Integer -> (Integer, Integer)
    normalise mantissa exponent
      | even mantissa = normalise (mantissa `div` 2) (exponent + 1)
      | otherwise = (mantissa, exponent)

-- |Checks whether or not the Double is within a safe range of operation.
isSafeInteger :: Double -> Bool
isSafeInteger x = case properFraction x of
  (n, f) -> f == 0.0 && minMantissa <= n && n <= maxMantissa

doubleRadix :: Integer
doubleRadix = floatRadix (undefined :: Double)

doubleDigits :: Int
doubleDigits = floatDigits (undefined :: Double)

doubleRange :: (Int, Int)
doubleRange = floatRange (undefined :: Double)

-- |The smallest representable mantissa. Simultaneously, the smallest integer which can be
--  represented as a Double without loss of precision.
minMantissa :: Integer
minMantissa = - maxMantissa

-- |The largest representable mantissa. Simultaneously, the largest integer which can be
--  represented as a Double without loss of precision.
maxMantissa :: Integer
maxMantissa = (doubleRadix ^ toInteger doubleDigits) - 1

-- |The largest representable exponent.
minExponent :: Integer
minExponent = toInteger $ (fst doubleRange - doubleDigits) - 1

-- |The smallest representable exponent.
maxExponent :: Integer
maxExponent = toInteger $ snd doubleRange - doubleDigits

-- |Encode a mantissa and an exponent as a Double.
doubleEncode :: Integer -> Integer -> Maybe Double
doubleEncode mantissa exponent
  = if minMantissa <= mantissa && mantissa <= maxMantissa &&
       minExponent <= exponent && exponent <= maxExponent
    then Just (encodeFloat mantissa (fromInteger exponent))
    else Nothing
