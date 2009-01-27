------------------------------------------------------------------------
-- Non-empty lists
------------------------------------------------------------------------

module Data.List.NonEmpty where

open import Data.Product hiding (map)
open import Data.Nat
import Data.Vec as Vec
open Vec using (Vec; []; _∷_)

infixr 5 _∷_ _++_

data List⁺ (A : Set) : Set where
  [_] : (x : A) → List⁺ A
  _∷_ : (x : A) (xs : List⁺ A) → List⁺ A

fromVec : ∀ {n A} → Vec A (suc n) → List⁺ A
fromVec {zero}  (x ∷ []) = [ x ]
fromVec {suc n} (x ∷ xs) = x ∷ fromVec xs

length_-1 : ∀ {A} → List⁺ A → ℕ
length [ x ]  -1 = 0
length x ∷ xs -1 = 1 + length xs -1

toVec : ∀ {A} (xs : List⁺ A) → Vec A (suc (length xs -1))
toVec [ x ]    = Vec.[_] x
toVec (x ∷ xs) = x ∷ toVec xs

lift : ∀ {A B} →
       (∀ {m} → Vec A (suc m) → ∃ λ n → Vec B (suc n)) →
       List⁺ A → List⁺ B
lift f xs = fromVec (proj₂ (f (toVec xs)))

map : ∀ {A B} → (A → B) → List⁺ A → List⁺ B
map f = lift (λ xs → (, Vec.map f xs))

_++_ : ∀ {A} → List⁺ A → List⁺ A → List⁺ A
xs ++ ys = lift (λ xs → (, Vec._++_ xs (toVec ys))) xs
