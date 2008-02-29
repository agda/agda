------------------------------------------------------------------------
-- Lists with fast append
------------------------------------------------------------------------

module Data.DifferenceList where

import Data.List as L
open L using ([_])
open import Data.Function

infixr 5 _∷_ _++_

DiffList : Set -> Set
DiffList a = [ a ] -> [ a ]

[] : forall {a} -> DiffList a
[] = const L.[]

_∷_ : forall {a} -> a -> DiffList a -> DiffList a
x ∷ xs = \k -> L._∷_ x (xs k)

singleton : forall {a} -> a -> DiffList a
singleton x = x ∷ []

_++_ : forall {a} -> DiffList a -> DiffList a -> DiffList a
xs ++ ys = \k -> xs (ys k)

toList : forall {a} -> DiffList a -> [ a ]
toList xs = xs L.[]

-- fromList xs is linear in the length of xs.

fromList : forall {a} -> [ a ] -> DiffList a
fromList xs = \k -> xs ⟨ L._++_ ⟩ k

-- It is OK to use L._++_ here, since map is linear in the length of
-- the list anyway.

map : forall {a b} -> (a -> b) -> DiffList a -> DiffList b
map f xs = \k -> L.map f (toList xs) ⟨ L._++_ ⟩ k

-- concat is linear in the length of the outer list.

concat : forall {a} -> DiffList (DiffList a) -> DiffList a
concat xs = concat' (toList xs)
  where
  concat' : forall {a} -> [ DiffList a ] -> DiffList a
  concat' = L.foldr _++_ []
