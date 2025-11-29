
{-# LANGUAGE MagicHash #-}

module Agda.Utils.PointerEquality where

import GHC.Exts (reallyUnsafePtrEquality#, isTrue#)

{-# INLINE ptrEq #-}
-- | Checks if two arguments are equal as pointers in memory.
ptrEq :: a -> a -> Bool
ptrEq x y = x `seq` y `seq` isTrue# (reallyUnsafePtrEquality# x y)

{-# INLINE copyCon1 #-}
copyCon1 :: b -> (a -> b) -> a -> a -> b
copyCon1 old f !a !a'
  | ptrEq a a' = old
  | otherwise  = f a'

{-# INLINE copyCon2 #-}
copyCon2 :: c -> (a -> b -> c) -> a -> a -> b -> b -> c
copyCon2 old f !a !a' !b !b'
  | ptrEq a a', ptrEq b b' = old
  | otherwise  = f a' b'

{-# INLINE copyCon3 #-}
copyCon3 :: d -> (a -> b -> c -> d) -> a -> a -> b -> b -> c -> c -> d
copyCon3 old f !a !a' !b !b' !c !c'
  | ptrEq a a', ptrEq b b', ptrEq c c' = old
  | otherwise  = f a' b' c'

{-# INLINE copyCon4 #-}
copyCon4 :: e -> (a -> b -> c -> d -> e) -> a -> a -> b -> b -> c -> c -> d -> d -> e
copyCon4 old f !a !a' !b !b' !c !c' !d !d'
  | ptrEq a a', ptrEq b b', ptrEq c c', ptrEq d d' = old
  | otherwise  = f a' b' c' d'

{-# INLINE copyCon5 #-}
copyCon5 :: f -> (a -> b -> c -> d -> e -> f) -> a -> a -> b -> b -> c -> c -> d -> d -> e -> e -> f
copyCon5 old f !a !a' !b !b' !c !c' !d !d' !e !e'
  | ptrEq a a', ptrEq b b', ptrEq c c', ptrEq d d', ptrEq e e' = old
  | otherwise  = f a' b' c' d' e'

{-# INLINE copyCon6 #-}
copyCon6 ::
  g -> (a -> b -> c -> d -> e -> f -> g) -> a -> a -> b -> b -> c -> c -> d -> d -> e -> e -> f -> f -> g
copyCon6 old fun !a !a' !b !b' !c !c' !d !d' !e !e' !f !f'
  | ptrEq a a', ptrEq b b', ptrEq c c', ptrEq d d', ptrEq e e', ptrEq f f' = old
  | otherwise  = fun a' b' c' d' e' f'

{-# INLINE mapCopy #-}
-- | Map over a list while avoiding copying.
mapCopy :: (a -> a) -> [a] -> [a]
mapCopy f = go where
  go as = case as of
    old@[]         -> old
    old@(!a : !as) -> copyCon2 old (:) a (f a) as (go as)
