
module _ where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

postulate
  C : Set → Set

record R (F : Nat → Set) : Set where
  field
    n : Nat
    ⦃ iC ⦄ : C (F n)

postulate
  T : Nat → Set
  instance
    iCT5 : C (T 5)

module _ (n m : Nat) where
  foo : n ≡ suc m → Nat → Set
  foo refl p = Nat
    where
      bar : R T
      R.n bar = 5
