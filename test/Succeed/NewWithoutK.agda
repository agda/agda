{-# OPTIONS --without-K #-}

module NewWithoutK where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

infixl 20 _+_
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

infixl 30 _*_
_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

infixl 5 _⊎_
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

infixl 10 _≡_
data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {m n : ℕ} → m ≤ n → suc m ≤ suc n

foo : (k l m : ℕ) → k ≡ l + m → ℕ
foo .(l + m) l m refl = zero

bar : (n : ℕ) → n ≤ n → ℕ
bar .zero z≤n = zero
bar .(suc m) (s≤s {m} p) = zero

baz : ∀ m n → m * n ≡ zero → m ≡ zero ⊎ n ≡ zero
baz zero     n      h = inj₁ refl
baz (suc m) zero    h = inj₂ refl
baz (suc x) (suc x₁) ()
