{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Utils.Suffix where

import Data.Char
import qualified Data.List as List

import Agda.Utils.Impossible

------------------------------------------------------------------------
-- Subscript digits

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
  = Prime     Integer  -- ^ Identifier ends in @Integer@ many primes.
  | Index     Integer  -- ^ Identifier ends in number @Integer@ (ordinary digits).
  | Subscript Integer  -- ^ Identifier ends in number @Integer@ (subscript digits).

-- | Increase the suffix by one.

nextSuffix :: Suffix -> Suffix
nextSuffix (Prime i)     = Prime $ i + 1
nextSuffix (Index i)     = Index $ i + 1
nextSuffix (Subscript i) = Subscript $ i + 1

-- | Parse suffix.

suffixView :: String -> (String, Maybe Suffix)
suffixView s
    | (ps@(_:_), s') <- span (=='\'') rs         = (reverse s', Just $ Prime $ List.genericLength ps)
    | (ns@(_:_), s') <- span isDigit rs          = (reverse s', Just $ Index $ read $ reverse ns)
    | (ns@(_:_), s') <- span isSubscriptDigit rs = (reverse s', Just $ Subscript $ read $
                                                      map fromSubscriptDigit $ reverse ns)
    | otherwise                                  = (s, Nothing)
    where rs = reverse s

-- Note: suffixView could be implemented using spanEnd, but the implementation using reverse
-- looks more efficient, since the reversal is only done once.
--
-- suffixView :: String -> (String, Maybe Suffix)
-- suffixView s
--     | (s', ps@(_:_)) <- spanEnd (=='\'') s         = (s', Just $ Prime $ length ps)
--     | (s', ns@(_:_)) <- spanEnd isDigit s          = (s', Just $ Index $ read ns)
--     | (s', ns@(_:_)) <- spanEnd isSubscriptDigit s = (s', Just $ Subscript $ read $ map fromSubscriptDigit ns)
--     | otherwise                                    = (s, Nothing)

-- | Print suffix.

renderSuffix :: Suffix -> String
renderSuffix (Prime n)     = List.genericReplicate n '\''
renderSuffix (Index i)     = show i
renderSuffix (Subscript i) = map toSubscriptDigit (show i)

addSuffix :: String -> Suffix -> String
addSuffix str suffix = str ++ renderSuffix suffix
