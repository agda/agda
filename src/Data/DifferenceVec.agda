------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors with fast append
------------------------------------------------------------------------

module Data.DifferenceVec where

open import Data.DifferenceNat
open import Data.Vec as V using (Vec)
open import Function
import Data.Nat.Base as N

infixr 5 _∷_ _++_

DiffVec : ∀ {ℓ} → Set ℓ → Diffℕ → Set ℓ
DiffVec A m = ∀ {n} → Vec A n → Vec A (m n)

[] : ∀ {a} {A : Set a} → DiffVec A 0#
[] = λ k → k

_∷_ : ∀ {a} {A : Set a} {n} → A → DiffVec A n → DiffVec A (suc n)
x ∷ xs = λ k → V._∷_ x (xs k)

[_] : ∀ {a} {A : Set a} → A → DiffVec A 1#
[ x ] = x ∷ []

_++_ : ∀ {a} {A : Set a} {m n} →
       DiffVec A m → DiffVec A n → DiffVec A (m + n)
xs ++ ys = λ k → xs (ys k)

toVec : ∀ {a} {A : Set a} {n} → DiffVec A n → Vec A (toℕ n)
toVec xs = xs V.[]

-- fromVec xs is linear in the length of xs.

fromVec : ∀ {a} {A : Set a} {n} → Vec A n → DiffVec A (fromℕ n)
fromVec xs = λ k → xs ⟨ V._++_ ⟩ k

head : ∀ {a} {A : Set a} {n} → DiffVec A (suc n) → A
head xs = V.head (toVec xs)

tail : ∀ {a} {A : Set a} {n} → DiffVec A (suc n) → DiffVec A n
tail xs = λ k → V.tail (xs k)

take : ∀ {a} {A : Set a} m {n} →
       DiffVec A (fromℕ m + n) → DiffVec A (fromℕ m)
take N.zero    xs = []
take (N.suc m) xs = head xs ∷ take m (tail xs)

drop : ∀ {a} {A : Set a} m {n} →
       DiffVec A (fromℕ m + n) → DiffVec A n
drop N.zero    xs = xs
drop (N.suc m) xs = drop m (tail xs)
