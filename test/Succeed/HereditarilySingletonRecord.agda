-- Modified: Andreas, 2011-04-11 freezing Metas
-- Modified: Andreas, 2016-09-20 explicit eta-equality declaration

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
    -- Andreas, 2016-09-20, after fixing issue #2197:
    -- Since we are in a mutual block, eta-equality is not switched on
    -- automatically while checking the mutual block (only after that).
    -- Thus, we turn it on manually.
    eta-equality
    field
      singleton : Unit one

  baz : HereditarilySingleton₂
  baz = _

  force : one ≡ suc zero
  force = refl
