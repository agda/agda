{-# OPTIONS --cubical-compatible --show-implicit #-}
-- {-# OPTIONS -v tc.lhs.split.well-formed:100 #-}
-- Andreas, adapted from Andres Sicard, 2013-05-29
module WithoutKRestrictive where

open import Common.Level
open import Common.Equality
open import Common.Product

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {n m} → n ≤ m → suc n ≤ suc m

_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

refl≤ : ∀ (n : ℕ) → n ≤ n
refl≤ zero    = z≤n
refl≤ (suc n) = s≤s (refl≤ n)

data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

length : {A : Set} → List A → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)

P : {A : Set} → List A → List A → Set
P xs ys = Σ _ (λ x → ys ≡ (x ∷ xs))

Q : {A : Set} → List A → List A → Set
Q xs ys = (length xs) < (length ys)

helper : {A : Set}(y : A)(xs : List A) → (length xs) < (length (y ∷ xs))
helper y []       = s≤s z≤n
helper y (x ∷ xs) = s≤s (refl≤ _)

-- Why the --cubical-compatible option rejects the following proof

foo : {A : Set}(xs ys : List A) → P xs ys → Q xs ys
foo xs .(x ∷ xs) (x , refl) = helper x xs

-- if I can prove foo using only subst

foo' : {A : Set}(xs ys : List A) → P xs ys → Q xs ys
foo' xs ys (x , h) =
  subst (λ ys' → length xs < length ys') (sym h) (helper x xs)
