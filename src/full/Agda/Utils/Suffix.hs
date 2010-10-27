{-# LANGUAGE PatternGuards #-}
module Agda.Utils.Suffix where

import Data.Char

data Suffix = NoSuffix | Prime Int | Index Int

nextSuffix NoSuffix  = Prime 1
nextSuffix (Prime _) = Index 0	-- we only use single primes in generated names
nextSuffix (Index i) = Index $ i + 1

suffixView :: String -> (String, Suffix)
suffixView s
    | (ps@(_:_), s') <- span (=='\'') rs = (reverse s', Prime $ length ps)
    | (ns@(_:_), s') <- span isDigit rs	 = (reverse s', Index $ read $ reverse ns)
    | otherwise				 = (s, NoSuffix)
    where
	rs = reverse s

addSuffix :: String -> Suffix -> String
addSuffix s NoSuffix = s
addSuffix s (Prime n) = s ++ replicate n '\''
addSuffix s (Index i) = s ++ show i
