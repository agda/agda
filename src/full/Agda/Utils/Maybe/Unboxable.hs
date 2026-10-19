{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE MagicHash #-}

module Agda.Utils.Maybe.Unboxable where

data Maybe# a = Maybe# (# a | (# #) #)

pattern Nothing# :: Maybe# a
pattern Nothing# = Maybe# (# | (# #) #)
pattern Just# :: a -> Maybe# a
pattern Just# a = Maybe# (# a | #)
{-# COMPLETE Nothing#, Just# #-}
