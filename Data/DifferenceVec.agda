------------------------------------------------------------------------
-- Vectors with fast append
------------------------------------------------------------------------

module Data.DifferenceVec where

open import Data.DifferenceNat
open import Data.Vec as V using (Vec)
open import Data.Function
import Data.Nat as N

infixr 5 _∷_ _++_

DiffVec : Set → Diffℕ → Set
DiffVec A m = ∀ {n} → Vec A n → Vec A (m n)

[] : ∀ {A} → DiffVec A 0#
[] = λ k → k

_∷_ : ∀ {A n} → A → DiffVec A n → DiffVec A (suc n)
x ∷ xs = λ k → V._∷_ x (xs k)

[_] : ∀ {A} → A → DiffVec A 1#
[ x ] = x ∷ []

_++_ : ∀ {A m n} → DiffVec A m → DiffVec A n → DiffVec A (m + n)
xs ++ ys = λ k → xs (ys k)

toVec : ∀ {A n} → DiffVec A n → Vec A (toℕ n)
toVec xs = xs V.[]

-- fromVec xs is linear in the length of xs.

fromVec : ∀ {A n} → Vec A n → DiffVec A (fromℕ n)
fromVec xs = λ k → xs ⟨ V._++_ ⟩ k

head : ∀ {A n} → DiffVec A (suc n) → A
head xs = V.head (toVec xs)

tail : ∀ {A n} → DiffVec A (suc n) → DiffVec A n
tail xs = λ k → V.tail (xs k)

take : ∀ {a} m {n} → DiffVec a (fromℕ m + n) → DiffVec a (fromℕ m)
take N.zero    xs = []
take (N.suc m) xs = head xs ∷ take m (tail xs)

drop : ∀ {a} m {n} → DiffVec a (fromℕ m + n) → DiffVec a n
drop N.zero    xs = xs
drop (N.suc m) xs = drop m (tail xs)
