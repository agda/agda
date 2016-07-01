
module _ where

data _==_ {A : Set} (a : A) : A → Set where
  refl : a == a

data ⊥ : Set where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

it : ∀ {a} {A : Set a} ⦃ x : A ⦄ → A
it ⦃ x ⦄ = x

f : (n : ℕ) ⦃ p : ⦃ _ : n == zero ⦄ → ⊥ ⦄ → ℕ
f n = n

g : (n : ℕ) ⦃ q : ⦃ _ : n == zero ⦄ → ⊥ ⦄ → ℕ
g n ⦃ q ⦄ = f n

h : (n : ℕ) ⦃ q : ⦃ _ : n == zero ⦄ → ⊥ ⦄ → ℕ
h n ⦃ q ⦄ = f n ⦃ it ⦄
