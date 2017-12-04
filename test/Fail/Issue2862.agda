-- Andreas, 2017-12-04, issue #2862, reported by m0davis
-- Regression in development version 2.5.4

-- Scope checker allowed definition in different module than signature

-- {-# OPTIONS -v scope.data.def:30 #-}

open import Agda.Builtin.Equality

data N : Set

module Z where
  data N where  -- should be rejected since signature lives in different module
    zero : N
  unitary-N : (x y : N) → x ≡ y
  unitary-N zero zero = refl

data N where
  zero : N
  suc : N → N

data ⊥ : Set where

one : N
one = suc zero

¬zero≡one : zero ≡ one → ⊥
¬zero≡one ()

zero≡one : zero ≡ one
zero≡one = Z.unitary-N zero one

boom : ⊥
boom = ¬zero≡one zero≡one
