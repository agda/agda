
open import Agda.Builtin.Nat

data Vec (A : Set) : Nat → Set where

variable
  A  : Set
  x  : A
  n  : Nat
  xs : Vec A n

postulate
  IsNil : Vec A 0 → Set

foo : (xs : Vec A n) → IsNil xs
foo = {!!}
