{-# OPTIONS --cubical-compatible --show-implicit #-}
-- {-# OPTIONS -v tc.lhs.split.well-formed:100 #-}
-- Andreas, adapted from Andres Sicard, 2013-05-29
module WithoutKRestrictiveNoUniPoly where

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

data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A

length : {A : Set} → List A → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

subst : {A : Set}(P : A → Set){a b : A} → a ≡ b → P a → P b
subst P refl x = x

sym : {A : Set}{a b : A} → a ≡ b → b ≡ a
sym refl = refl

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
