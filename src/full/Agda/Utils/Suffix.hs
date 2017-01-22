{-# LANGUAGE CPP #-}

module Agda.Utils.Suffix where

import Data.Char

import Agda.Utils.Function

#include "undefined.h"
import Agda.Utils.Impossible

------------------------------------------------------------------------
-- Subscript digits

-- | Is the character one of the subscripts @'₀'@-@'₉'@?

isSubscriptDigit :: Char -> Bool
isSubscriptDigit c = '₀' <= c && c <= '₉'

-- | Converts @'0'@-@'9'@ to @'₀'@-@'₉'@.
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
  | isSubscriptDigit d =
      toEnum (fromEnum '0' + (fromEnum d - fromEnum '₀'))
  | otherwise          = __IMPOSSIBLE__

------------------------------------------------------------------------
-- Suffices

-- | Classification of identifier variants.

data Suffix
  = NoSuffix
  | Prime     Int  -- ^ Identifier ends in @Int@ many primes.
  | Index     Int  -- ^ Identifier ends in number @Int@ (ordinary digits).
  | Subscript Int  -- ^ Identifier ends in number @Int@ (subscript digits).

-- | Increase the suffix by one.  If no suffix yet, put a subscript @1@.

nextSuffix :: Suffix -> Suffix
nextSuffix NoSuffix      = Subscript 1
nextSuffix (Prime i)     = Prime $ i + 1
nextSuffix (Index i)     = Index $ i + 1
nextSuffix (Subscript i) = Subscript $ i + 1

-- | Parse suffix.

suffixView :: String -> (String, Suffix)
suffixView s
    | (ps@(_:_), s') <- span (=='\'') rs         = (reverse s', Prime $ length ps)
    | (ns@(_:_), s') <- span isDigit rs          = (reverse s', Index $ read $ reverse ns)
    | (ns@(_:_), s') <- span isSubscriptDigit rs = (reverse s',
                                                    Subscript $ read $
                                                      map fromSubscriptDigit $ reverse ns)
    | otherwise                                  = (s, NoSuffix)
    where rs = reverse s

-- | Print suffix.

addSuffix :: String -> Suffix -> String
addSuffix s NoSuffix      = s
addSuffix s (Prime n)     = s ++ replicate n '\''
addSuffix s (Index i)     = s ++ show i
addSuffix s (Subscript i) = s ++ map toSubscriptDigit (show i)

-- | Add first available @Suffix@ to a name.

nameVariant
  :: (String -> Bool) -- ^ Is the given name already taken?
  -> String           -- ^ Name of which we want an available variant.
  -> String           -- ^ Name extended by suffix that is not taken already.
nameVariant taken x
  | taken x   = addSuffix x $ trampoline step $ Subscript 1
  | otherwise = x
  where
    -- if the current suffix is taken, repeat with next suffix, else done
    step s = if taken (addSuffix x s) then Right (nextSuffix s) else Left s
