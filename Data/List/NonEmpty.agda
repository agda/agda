------------------------------------------------------------------------
-- Non-empty lists
------------------------------------------------------------------------

module Data.List.NonEmpty where

open import Data.Product
open import Data.Nat
import Data.Vec as Vec
open Vec using (Vec; []; _∷_)

infixr 5 _∷_ _++_

data List⁺ (A : Set) : Set where
  [_] : (x : A) -> List⁺ A
  _∷_ : (x : A) (xs : List⁺ A) -> List⁺ A

fromVec : forall {A n} -> Vec A (suc n) -> List⁺ A
fromVec (x ∷ [])     = [ x ]
fromVec (x ∷ y ∷ xs) = x ∷ fromVec (y ∷ xs)

length_-1 : forall {A} -> List⁺ A -> ℕ
length [ x ]  -1 = 0
length x ∷ xs -1 = 1 + length xs -1

toVec : forall {A} (xs : List⁺ A) -> Vec A (suc (length xs -1))
toVec [ x ]    = Vec.[_] x
toVec (x ∷ xs) = x ∷ toVec xs

lift : forall {A B} ->
       (forall {m} -> Vec A (suc m) -> ∃ \n -> Vec B (suc n)) ->
       List⁺ A -> List⁺ B
lift f xs = fromVec (proj₂ (f (toVec xs)))

map : forall {A B} -> (A -> B) -> List⁺ A -> List⁺ B
map f = lift (\xs -> (, Vec.map f xs))

_++_ : forall {A} -> List⁺ A -> List⁺ A -> List⁺ A
xs ++ ys = lift (\xs -> (, Vec._++_ xs (toVec ys))) xs
