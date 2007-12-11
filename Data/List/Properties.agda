------------------------------------------------------------------------
-- List-related properties
------------------------------------------------------------------------

module Data.List.Properties where

open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Function
open import Logic
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Algebra

map-++-commute :  forall {a b} (f : a -> b) xs ys
               -> map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute f []       ys = ≡-refl
map-++-commute f (x ∷ xs) ys =
  ≡-cong (_∷_ (f x)) (map-++-commute f xs ys)

sum-++-commute : forall xs ys -> sum (xs ++ ys) ≡ sum xs + sum ys
sum-++-commute []       ys = ≡-refl
sum-++-commute (x ∷ xs) ys = begin
  x + sum (xs ++ ys)
                         ≡⟨ ≡-cong (_+_ x) (sum-++-commute xs ys) ⟩
  x + (sum xs + sum ys)
                         ≡⟨ sym $ +-assoc x _ _ ⟩
  (x + sum xs) + sum ys
                         ∎
  where open CommutativeSemiring ℕ-commutativeSemiring hiding (_+_)
