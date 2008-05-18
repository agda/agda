
module Data.Map
    (Key  : Set)
  where

import Data.Bool
import Data.Maybe

open   Data.Bool

infix 40 _<_ _>_

postulate
  _<_  : Key -> Key -> Bool

_>_ : Key -> Key -> Bool
x > y = y < x

private
  data Map' (a : Set) : Set where
    leaf : Map' a
    node : Key -> a -> Map' a -> Map' a -> Map' a

Map : Set -> Set
Map = Map'

empty : {a : Set} -> Map a
empty = leaf

{-
insert : {a : Set} -> Key -> a -> Map a -> Map a
insert k v leaf = node k v leaf leaf
insert k v (node k' v' l r) =
  | k < k' => node k' v' (insert k v l) r
  | k > k' => node k' v' l (insert k v r)
  | otherwise node k' v l r
-}

open Data.Maybe

{-
lookup : {a : Set} -> Key -> Map a -> Maybe a
lookup k leaf = nothing
lookup k (node k' v l r) =
  | k < k' => lookup k l
  | k > k' => lookup k r
  | otherwise just v
-}
