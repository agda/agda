------------------------------------------------------------------------
-- Lists with fast append
------------------------------------------------------------------------

module Data.DifferenceList where

open import Data.List as L using (List)
open import Data.Function
open import Data.Nat

infixr 5 _∷_ _++_

DiffList : Set → Set
DiffList a = List a → List a

lift : ∀ {a} → (List a → List a) → (DiffList a → DiffList a)
lift f xs = λ k → f (xs k)

[] : ∀ {a} → DiffList a
[] = λ k → k

_∷_ : ∀ {a} → a → DiffList a → DiffList a
_∷_ x = lift (L._∷_ x)

[_] : ∀ {a} → a → DiffList a
[ x ] = x ∷ []

_++_ : ∀ {a} → DiffList a → DiffList a → DiffList a
xs ++ ys = λ k → xs (ys k)

toList : ∀ {a} → DiffList a → List a
toList xs = xs L.[]

-- fromList xs is linear in the length of xs.

fromList : ∀ {a} → List a → DiffList a
fromList xs = λ k → xs ⟨ L._++_ ⟩ k

-- It is OK to use L._++_ here, since map is linear in the length of
-- the list anyway.

map : ∀ {a b} → (a → b) → DiffList a → DiffList b
map f xs = λ k → L.map f (toList xs) ⟨ L._++_ ⟩ k

-- concat is linear in the length of the outer list.

concat : ∀ {a} → DiffList (DiffList a) → DiffList a
concat xs = concat' (toList xs)
  where
  concat' : ∀ {a} → List (DiffList a) → DiffList a
  concat' = L.foldr _++_ []

take : ∀ {a} → ℕ → DiffList a → DiffList a
take n = lift (L.take n)

drop : ∀ {a} → ℕ → DiffList a → DiffList a
drop n = lift (L.drop n)
