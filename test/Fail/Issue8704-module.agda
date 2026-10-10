{-# OPTIONS --safe --without-K #-}

-- Issue #8704, variant with a child module.
--
-- In an abstract block, we unfold the abstract definitions of the current
-- module and its parents.  So the solution of an abstract meta created in a
-- parent module must not depend on the abstract definitions of a child module.

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data IsNat : Nat → Set where
  isZero : IsNat zero
  isSuc  : (n : Nat) → IsNat (suc n)

-- We use a where block so that the metas are not frozen too early.

dummy : Nat
dummy = zero
  where
  module Parent where

    abstract
      N : Set
      N = _
      leak : N
      leak = _

    data MkLeak : N → Set where
      mk : (w : N) → MkLeak w

    module Child where

      abstract
        secret : Nat
        secret = suc zero

        -- This solves N := IsNat secret, which is fine.
        fixN : N ≡ IsNat secret
        fixN = refl

      abstract
        -- This should not solve leak := isSuc zero, which is well-typed
        -- in Child where secret unfolds, but not in Parent where it does not.
        solve : MkLeak leak
        solve = mk (isSuc zero)
