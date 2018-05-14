
open import Agda.Builtin.Nat

postulate P : Nat → Set

record R : Set where
  field
    f : P zero

foo : R → Set
foo (record { f = f0 }) with zero
foo r | x = Nat
