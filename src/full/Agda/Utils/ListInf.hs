-- | Infinite lists (streams).
--
-- Wrapper for "Data.List.Infinite" from the @infinite-list@ package
-- that generalizes some type signatures, using 'Integral' for indexing,
-- and adds some missing functions.
--
-- Import this module as follows:
--
-- @
-- import Agda.Utils.ListInf (ListInf, pattern (:<))
-- import Agda.Utils.ListInf qualified as ListInf
-- @
--
-- Motivation: lists constructed by 'repeat', 'iterate', 'cycle' etc.
-- are infinite, so the nil case can never arise when consuming them,
-- e.g. in a 'take' or 'zipWith'.
-- Constructing them as properly infinite lists ('ListInf') should thus
-- lead to slightly more efficient code, eliminating impossible cases.

module Agda.Utils.ListInf
  ( module Agda.Utils.ListInf, module Inf)
  where

import Prelude
  ( Enum, Foldable, Functor, Int, Integral
  , (.), ($), (-), (<=), (>)
  , fromIntegral, id, otherwise, succ
  )

import Data.List.Infinite qualified
import Data.List.Infinite as Inf
  ( pattern (:<), cycle, iterate, prependList, repeat
  , head, tail
  , zip, zipWith
  ) -- add more as needed

type ListInf = Data.List.Infinite.Infinite

---------------------------------------------------------------------------
-- * Construction

-- | There is only one meaningful way to concatenate a finite and an infinite list,
-- justifying the name @append = prependList@.
append :: [a] -> ListInf a -> ListInf a
append = prependList

-- | @pad as b@ implements the frequent pattern @as ++ repeat b@.
pad :: [a] -> a -> ListInf a
pad as b = append as (repeat b)

-- | @upFrom n = [n..]@ as properly infinite list.
{-# SPECIALIZE upFrom :: Int -> ListInf Int #-}
upFrom :: Enum n => n -> ListInf n
upFrom = iterate succ

---------------------------------------------------------------------------
-- * Selection

-- | Update the @n@th element of an infinite list.
--   @Θ(n)@.
--
--   Precondition: the index @n@ is >= 0.
{-# SPECIALIZE updateAt :: Int -> (a -> a) -> ListInf a -> ListInf a #-}
updateAt :: Integral n => n -> (a -> a) -> ListInf a -> ListInf a
updateAt n f (a :< as)
  | n > 0     = a :< updateAt (n - 1) f as
  | otherwise = f a :< as

-- Generalized versions of the functions from the @infinite-list@ package:

{-# SPECIALIZE (!!) :: ListInf a -> Int -> a #-}
(!!) :: Integral n => ListInf a -> n -> a
as !! n = as Data.List.Infinite.!! fromIntegral n

{-# SPECIALIZE take :: Int -> ListInf a -> [a] #-}
take :: Integral n => n -> ListInf a -> [a]
take = Data.List.Infinite.genericTake

{-# SPECIALIZE drop :: Int -> ListInf a -> ListInf a #-}
drop :: Integral n => n -> ListInf a -> ListInf a
drop = Data.List.Infinite.genericDrop

-- | @splitAt n as == (take n as, drop n as)@
{-# SPECIALIZE splitAt :: Int -> ListInf a -> ([a], ListInf a) #-}
splitAt :: Integral n => n -> ListInf a -> ([a], ListInf a)
splitAt = Data.List.Infinite.genericSplitAt
