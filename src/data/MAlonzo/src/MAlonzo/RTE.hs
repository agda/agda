{-# LANGUAGE CPP #-}
module MAlonzo.RTE where

import Unsafe.Coerce
#if __GLASGOW_HASKELL__ >= 802
import qualified GHC.Exts as GHC (Any)
#else
import qualified GHC.Prim as GHC (Any)
#endif
import qualified Data.Word
import Numeric.IEEE ( IEEE(identicalIEEE) )

type AgdaAny = GHC.Any

-- Special version of coerce that plays well with rules.
{-# INLINE [1] coe #-}
coe :: a -> b
coe = unsafeCoerce
{-# RULES "coerce-id" forall (x :: a) . coe x = x #-}

-- Builtin QNames.
data QName = QName { nameId, moduleId :: Integer, qnameString :: String, qnameFixity :: Fixity }

data Assoc      = NonAssoc | LeftAssoc | RightAssoc
data Precedence = Unrelated | Related Integer
data Fixity     = Fixity Assoc Precedence

instance Eq QName where
  QName a b _ _ == QName c d _ _ = (a, b) == (c, d)

instance Ord QName where
  compare (QName a b _ _) (QName c d _ _) = compare (a, b) (c, d)

erased :: a
erased = coe (\ _ -> erased)

mazIncompleteMatch :: String -> a
mazIncompleteMatch s = error ("Agda: incomplete pattern matching: " ++ s)

mazUnreachableError :: a
mazUnreachableError = error ("Agda: unreachable code reached.")

addInt :: Integer -> Integer -> Integer
addInt = (+)

subInt :: Integer -> Integer -> Integer
subInt = (-)

mulInt :: Integer -> Integer -> Integer
mulInt = (*)

geqInt :: Integer -> Integer -> Bool
geqInt = (>=)

ltInt :: Integer -> Integer -> Bool
ltInt = (<)

eqInt :: Integer -> Integer -> Bool
eqInt = (==)

quotInt :: Integer -> Integer -> Integer
quotInt = quot

remInt :: Integer -> Integer -> Integer
remInt = rem

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

-- Words --

type Word64 = Data.Word.Word64

word64ToNat :: Word64 -> Integer
word64ToNat = fromIntegral

word64FromNat :: Integer -> Word64
word64FromNat = fromIntegral

{-# INLINE add64 #-}
add64 :: Word64 -> Word64 -> Word64
add64 = (+)

{-# INLINE sub64 #-}
sub64 :: Word64 -> Word64 -> Word64
sub64 = (-)

{-# INLINE mul64 #-}
mul64 :: Word64 -> Word64 -> Word64
mul64 = (*)

{-# INLINE quot64 #-}
quot64 :: Word64 -> Word64 -> Word64
quot64 = quot

{-# INLINE rem64 #-}
rem64 :: Word64 -> Word64 -> Word64
rem64 = rem

{-# INLINE eq64 #-}
eq64 :: Word64 -> Word64 -> Bool
eq64 = (==)

{-# INLINE lt64 #-}
lt64 :: Word64 -> Word64 -> Bool
lt64 = (<)

-- Support for musical coinduction.

data Inf a            = Sharp { flat :: a }
type Infinity level a = Inf a
