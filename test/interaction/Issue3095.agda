-- Andreas, 2018-05-28, issue #3095, cannot make hidden shadowing variable visible
-- Andreas, 2019-07-15, issue #3919, make hidden variable visible in par. module

module _ (A : Set) where

data Nat : Set where
  suc : {n : Nat} → Nat

data IsSuc : Nat → Set where
  isSuc : ∀{n} → IsSuc (suc {n})

test : ∀{n} → IsSuc n → Set
test p = aux p
  where
  aux : ∀{n} → IsSuc n → Set
  aux isSuc = {!n!}  -- Split on n here

-- Context:
-- p  : IsSuc n
-- n : Nat  (not in scope)
-- n₁ : Nat  (not in scope)

-- WAS: ERROR
-- Ambiguous variable n
-- when checking that the expression ? has type Set

open import Agda.Builtin.Equality

issue3919 : {n m : Nat} → n ≡ m
issue3919 = {!m!}
