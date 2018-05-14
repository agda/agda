-- Reported by Nisse on 2018-03-13

-- The `x` in the parent pattern was eta-expanded to `record{}`,
-- but with-abstraction didn't like this.

open import Agda.Builtin.Equality

record R : Set where

postulate
  easy : (A : Set) → A

F : (x : R) → Set₁
F x with easy (x ≡ x)
F x | refl with Set
F x | refl | _ = Set

-- OLD ERROR:
-- With clause pattern x is not an instance of its parent pattern
-- record {}

-- Fixed by allowing parent patterns to be replaced by variables
-- in the with clause (but checking that their instantiation is
-- type-correct).
