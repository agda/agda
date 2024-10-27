{-# LANGUAGE PolyKinds #-}

module MAlonzo.RTE where

import Prelude
  ( Bool, Char, Double, Integer, String
  , Enum(..), Eq(..), Ord(..), Integral(..), Num(..)
  , ($), error, otherwise
  , (++), fromIntegral
  )

import Data.Char ( GeneralCategory(Surrogate), generalCategory )
import Data.Kind ( Type)
import qualified Data.Word
import qualified GHC.Exts as GHC ( Any )
import Unsafe.Coerce ( unsafeCoerce )

type AgdaAny = GHC.Any

-- Special version of coerce that plays well with rules.
{-# INLINE [1] coe #-}
coe :: a -> b
coe = unsafeCoerce
{-# RULES "coerce-id" forall (x :: a) . coe x = x #-}

-- Builtin QNames.
data QName = QName { nameId, moduleId :: Integer, qnameString :: String, qnameFixity :: Fixity }

data Assoc      = NonAssoc | LeftAssoc | RightAssoc
data Precedence = Unrelated | Related PrecedenceLevel
data Fixity     = Fixity Assoc Precedence
type PrecedenceLevel = Double

instance Eq QName where
  QName a b _ _ == QName c d _ _ = (a, b) == (c, d)

instance Ord QName where
  compare (QName a b _ _) (QName c d _ _) = compare (a, b) (c, d)

erased :: a
erased = coe (\ _ -> erased)

mazUnreachableError :: a
mazUnreachableError = error ("Agda: unreachable code reached.")

mazHole :: String -> a
mazHole s = error ("Agda: reached hole: " ++ s)

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

-- #4999: Data.Text maps surrogate code points (\xD800 - \xDFFF) to the replacement character
-- \xFFFD, so to keep strings isomorphic to list of characters we do the same for characters.
natToChar :: Integer -> Char
natToChar n | generalCategory c == Surrogate = '\xFFFD'
            | otherwise                      = c
  where c = toEnum $ fromIntegral $ mod n 0x110000

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

data Inf                      a = Sharp { flat :: a }
type Infinity (level :: Type) a = Inf a
