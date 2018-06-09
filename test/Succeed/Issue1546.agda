-- Andreas, 2015-06-11
-- testing with in copattern matching with dependent record

-- {-# OPTIONS -v tc.with:20 #-}

open import Common.Prelude
open import Common.Equality

data Dec (P : Set) : Set where
  yes : (p : P) → Dec P
  no  : (¬p : P → ⊥) → Dec P

postulate
  _≟_ : (n m : Nat) → Dec (n ≡ m)
  boring : {A : Set} → A

record R : Set₁ where
  field
    Car  : Set
    el   : Car
    same : (x : Car) → Dec (x ≡ el)

test : (n : Nat) → R
R.Car  (test n) = Nat
R.el   (test n) = n
R.same (test zero) zero = yes refl
R.same (test zero) (suc x) = no λ()
R.same (test (suc n)) zero = no λ()
R.same (test (suc n)) (suc x) with n ≟ x
R.same (test (suc n)) (suc .n) | yes refl = yes refl
R.same (test (suc n)) (suc x) | no ¬p = no boring
