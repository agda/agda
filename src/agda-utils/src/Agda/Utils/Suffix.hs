
module Agda.Utils.Suffix where

import Data.Char

import Agda.Utils.Impossible

import Data.IORef
import qualified System.IO.Unsafe as UNSAFE
import Agda.Interaction.Options.IORefs

------------------------------------------------------------------------
-- Subscript digits

-- | Are we allowed to use unicode supscript characters?
subscriptAllowed :: UnicodeOrAscii
subscriptAllowed = UNSAFE.unsafePerformIO (readIORef unicodeOrAscii)

-- | Is the character one of the subscripts @'₀'@-@'₉'@?

isSubscriptDigit :: Char -> Bool
isSubscriptDigit c = '₀' <= c && c <= '₉'

-- | Converts @'0'@-@'9'@ to @'₀'@-@'₉'@
--
-- Precondition: The digit needs to be in range.

toSubscriptDigit :: Char -> Char
toSubscriptDigit d
  | isDigit d = toEnum (fromEnum '₀' + (fromEnum d - fromEnum '0'))
  | otherwise = __IMPOSSIBLE__

-- | Converts @'₀'@-@'₉'@ to @'0'@-@'9'@.
--
-- Precondition: The digit needs to be in range.

fromSubscriptDigit :: Char -> Char
fromSubscriptDigit d
  | isSubscriptDigit d = toEnum (fromEnum '0' + (fromEnum d - fromEnum '₀'))
  | otherwise          = __IMPOSSIBLE__

------------------------------------------------------------------------
-- Suffices

-- | Classification of identifier variants.

data Suffix
  = NoSuffix
  | Prime     Int  -- ^ Identifier ends in @Int@ many primes.
  | Index     Int  -- ^ Identifier ends in number @Int@ (ordinary digits).
  | Subscript Int  -- ^ Identifier ends in number @Int@ (subscript digits).

-- | Increase the suffix by one.  If no suffix yet, put a subscript @1@
--   unless users do not want us to use any unicode.

nextSuffix :: Suffix -> Suffix
nextSuffix NoSuffix      = case subscriptAllowed of
  UnicodeOk -> Subscript 1
  AsciiOnly -> Index 1
nextSuffix (Prime i)     = Prime $ i + 1
nextSuffix (Index i)     = Index $ i + 1
nextSuffix (Subscript i) = Subscript $ i + 1

-- | Parse suffix.

suffixView :: String -> (String, Suffix)
suffixView s
    | (ps@(_:_), s') <- span (=='\'') rs         = (reverse s', Prime $ length ps)
    | (ns@(_:_), s') <- span isDigit rs          = (reverse s', Index $ read $ reverse ns)
    | (ns@(_:_), s') <- span isSubscriptDigit rs = (reverse s', Subscript $ read $
                                                      map fromSubscriptDigit $ reverse ns)
    | otherwise                                  = (s, NoSuffix)
    where rs = reverse s

-- | Print suffix.

addSuffix :: String -> Suffix -> String
addSuffix s NoSuffix      = s
addSuffix s (Prime n)     = s ++ replicate n '\''
addSuffix s (Index i)     = s ++ show i
addSuffix s (Subscript i) = s ++ map toSubscriptDigit (show i)
