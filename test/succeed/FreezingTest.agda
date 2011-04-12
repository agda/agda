module FreezingTest where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

force : let one : ℕ
            one = _         -- this meta is not frozen after the end of let
        in  one ≡ suc zero
force = refl
