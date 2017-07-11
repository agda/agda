-- Andreas, 2017-07-11, issue #2639 reported by nad
--
-- Unsolvable size constraints were added to the constraint set
-- each time the size solver ran.  This lead to exponentially
-- many size constraints.

-- {-# OPTIONS -v tc.size.solve:40 #-}

module Issue2639 (A : Set) where

open import Agda.Builtin.Nat
open import Agda.Builtin.Size

open import Issue2639.DR A

postulate
  P : {i : Size} → D i → Set

F : Set₁
F = Set
  where

  -- This postulate creates an unsolved size constraint.
  postulate
    unused : P a

  G : Nat → Set → Set₁
  G zero = λ { _ → Set }
  G (suc zero) = λ { _ → Set }
  G (suc (suc zero)) = λ { _ → Set }
  G (suc (suc (suc zero))) = λ { _ → Set }
  G (suc (suc (suc (suc zero)))) = λ { _ → Set }
  G _ = λ { _ → Set }
