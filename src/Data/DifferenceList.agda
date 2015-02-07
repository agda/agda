------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists with fast append
------------------------------------------------------------------------

module Data.DifferenceList where

open import Data.List.Base as L using (List)
open import Function
open import Data.Nat.Base

infixr 5 _∷_ _++_

DiffList : ∀ {ℓ} → Set ℓ → Set ℓ
DiffList A = List A → List A

lift : ∀ {a} {A : Set a} →
       (List A → List A) → (DiffList A → DiffList A)
lift f xs = λ k → f (xs k)

[] : ∀ {a} {A : Set a} → DiffList A
[] = λ k → k

_∷_ : ∀ {a} {A : Set a} → A → DiffList A → DiffList A
_∷_ x = lift (L._∷_ x)

[_] : ∀ {a} {A : Set a} → A → DiffList A
[ x ] = x ∷ []

_++_ : ∀ {a} {A : Set a} → DiffList A → DiffList A → DiffList A
xs ++ ys = λ k → xs (ys k)

toList : ∀ {a} {A : Set a} → DiffList A → List A
toList xs = xs L.[]

-- fromList xs is linear in the length of xs.

fromList : ∀ {a} {A : Set a} → List A → DiffList A
fromList xs = λ k → xs ⟨ L._++_ ⟩ k

-- It is OK to use L._++_ here, since map is linear in the length of
-- the list anyway.

map : ∀ {a b} {A : Set a} {B : Set b} →
      (A → B) → DiffList A → DiffList B
map f xs = λ k → L.map f (toList xs) ⟨ L._++_ ⟩ k

-- concat is linear in the length of the outer list.

concat : ∀ {a} {A : Set a} → DiffList (DiffList A) → DiffList A
concat xs = concat' (toList xs)
  where
  concat' : ∀ {a} {A : Set a} → List (DiffList A) → DiffList A
  concat' = L.foldr _++_ []

take : ∀ {a} {A : Set a} → ℕ → DiffList A → DiffList A
take n = lift (L.take n)

drop : ∀ {a} {A : Set a} → ℕ → DiffList A → DiffList A
drop n = lift (L.drop n)
