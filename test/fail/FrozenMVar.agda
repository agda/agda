-- Andreas, 2011-04-11
-- taken from test/succeed/HereditarilySingletonRecord.agda

module FrozenMVar where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

one : ℕ
one = _

force : one ≡ suc zero
force = refl
-- this tries to instantiate the frozen metavar for one