-- Modified: Andreas, 2011-04-11 freezing Metas
module HereditarilySingletonRecord where

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- * trivial unit type

record Singleton : Set where

foo : Singleton
foo = _

-- * product of unit types

record HereditarilySingleton : Set where
  field
    singleton      : Singleton
    also-singleton : Singleton

bar : HereditarilySingleton
bar = _

-- * hiding the unit types behind a type case

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

Unit : ℕ → Set
Unit zero    = Singleton
Unit (suc n) = Unit n

mutual -- needed to avoid freezing

  one : ℕ
  one = _
  
  record HereditarilySingleton₂ : Set where
    field
      singleton : Unit one
  
  baz : HereditarilySingleton₂
  baz = _
  
  force : one ≡ suc zero
  force = refl
