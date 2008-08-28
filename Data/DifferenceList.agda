------------------------------------------------------------------------
-- Lists with fast append
------------------------------------------------------------------------

module Data.DifferenceList where

import Data.List as L
open L using (List)
open import Data.Function
open import Data.Nat

infixr 5 _∷_ _++_

DiffList : Set -> Set
DiffList a = List a -> List a

lift : forall {a} -> (List a -> List a) -> (DiffList a -> DiffList a)
lift f xs = \k -> f (xs k)

[] : forall {a} -> DiffList a
[] = \k -> k

_∷_ : forall {a} -> a -> DiffList a -> DiffList a
_∷_ x = lift (L._∷_ x)

[_] : forall {a} -> a -> DiffList a
[ x ] = x ∷ []

_++_ : forall {a} -> DiffList a -> DiffList a -> DiffList a
xs ++ ys = \k -> xs (ys k)

toList : forall {a} -> DiffList a -> List a
toList xs = xs L.[]

-- fromList xs is linear in the length of xs.

fromList : forall {a} -> List a -> DiffList a
fromList xs = \k -> xs ⟨ L._++_ ⟩ k

-- It is OK to use L._++_ here, since map is linear in the length of
-- the list anyway.

map : forall {a b} -> (a -> b) -> DiffList a -> DiffList b
map f xs = \k -> L.map f (toList xs) ⟨ L._++_ ⟩ k

-- concat is linear in the length of the outer list.

concat : forall {a} -> DiffList (DiffList a) -> DiffList a
concat xs = concat' (toList xs)
  where
  concat' : forall {a} -> List (DiffList a) -> DiffList a
  concat' = L.foldr _++_ []

take : forall {a} -> ℕ -> DiffList a -> DiffList a
take n = lift (L.take n)

drop : forall {a} -> ℕ -> DiffList a -> DiffList a
drop n = lift (L.drop n)
