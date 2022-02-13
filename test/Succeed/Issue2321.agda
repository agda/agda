{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Coinduction
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Nat

infixr 5 _∷_

data Stream (A : Set) : Set where
  _∷_ : (x : A) (xs : ∞ (Stream A)) → Stream A

head : ∀ {A} → Stream A → A
head (x ∷ xs) = x

tail : ∀ {A} → Stream A → Stream A
tail (x ∷ xs) = ♭ xs

take : ∀ {A} (n : Nat) → Stream A → List A
take zero    xs       = []
take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

accepted : ∀ {A} {n} (xs : Stream A) →
           take (suc n) xs ≡ take (suc n) (head xs ∷ ♯ tail xs)
accepted (x ∷ xs) = refl

private
  rejected : ∀ {A} {n} (xs : Stream A) →
             take (suc n) xs ≡ take (suc n) (head xs ∷ ♯ tail xs)
  rejected (x ∷ xs) = refl
