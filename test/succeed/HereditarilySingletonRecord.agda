module HereditarilySingletonRecord where

record Singleton : Set where

record HereditarilySingleton : Set where
  field
    singleton : Singleton

foo : Singleton
foo = _

bar : HereditarilySingleton
bar = _

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

Unit : ℕ → Set
Unit zero    = Singleton
Unit (suc n) = Unit n

one : ℕ
one = _

record HereditarilySingleton₂ : Set where
  field
    singleton : Unit one

baz : HereditarilySingleton₂
baz = _

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

force : one ≡ suc zero
force = refl
