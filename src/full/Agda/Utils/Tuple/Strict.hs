-- | Complement "Data.Strict.Tuple".

module Agda.Utils.Tuple.Strict (module Agda.Utils.Tuple.Strict, module Data.Strict.Tuple) where

import Data.Strict.Tuple

-- | Strict version of '(&&&)'.

infixr 3 &!&

(&!&) :: (a -> b) -> (a -> c) -> a -> Pair b c
(&!&) f g !a = f a :!: g a
