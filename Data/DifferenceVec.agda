------------------------------------------------------------------------
-- Vectors with fast append
------------------------------------------------------------------------

module Data.DifferenceVec where

open import Data.DifferenceNat
import Data.Vec as V
open V using (Vec)
open import Data.Function
import Data.Nat as N

infixr 5 _∷_ _++_

DiffVec : Set -> Diffℕ -> Set
DiffVec A m = forall {n} -> Vec A n -> Vec A (m n)

[] : forall {A} -> DiffVec A 0#
[] = \k -> k

_∷_ : forall {A n} -> A -> DiffVec A n -> DiffVec A (suc n)
x ∷ xs = \k -> V._∷_ x (xs k)

[_] : forall {A} -> A -> DiffVec A 1#
[ x ] = x ∷ []

_++_ : forall {A m n} -> DiffVec A m -> DiffVec A n -> DiffVec A (m + n)
xs ++ ys = \k -> xs (ys k)

toVec : forall {A n} -> DiffVec A n -> Vec A (toℕ n)
toVec xs = xs V.[]

-- fromVec xs is linear in the length of xs.

fromVec : forall {A n} -> Vec A n -> DiffVec A (fromℕ n)
fromVec xs = \k -> xs ⟨ V._++_ ⟩ k

head : forall {A n} -> DiffVec A (suc n) -> A
head xs = V.head (toVec xs)

tail : forall {A n} -> DiffVec A (suc n) -> DiffVec A n
tail xs = \k -> V.tail (xs k)

take : forall {a} m {n} ->
       DiffVec a (fromℕ m + n) -> DiffVec a (fromℕ m)
take N.zero    xs = []
take (N.suc m) xs = head xs ∷ take m (tail xs)

drop : forall {a} m {n} ->
       DiffVec a (fromℕ m + n) -> DiffVec a n
drop N.zero    xs = xs
drop (N.suc m) xs = drop m (tail xs)
