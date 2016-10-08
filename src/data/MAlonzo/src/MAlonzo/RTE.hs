module MAlonzo.RTE where

import Unsafe.Coerce
import GHC.Prim
import Numeric.IEEE ( IEEE(identicalIEEE) )

-- Special version of coerce that plays well with rules.
{-# INLINE [1] coe #-}
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
  | otherwise                  = compare x y
  where
    isNegInf z = z < 0 && isInfinite z

ltNumFloat :: Double -> Double -> Bool
ltNumFloat x y = case compareFloat x y of
                LT -> True
                _  -> False
