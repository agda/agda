{-# OPTIONS --allow-unsolved-metas #-}

postulate
  Nat : Set
  Fin : Nat → Set
  Foo : (n : Nat) → Fin n → Set
  Bar : ∀ {n m} → Foo n m → Set

variable
  n : Nat
  m : Fin _
  k : Foo _ m
  l : Foo n m

open import Agda.Builtin.Equality

postulate
  goal-type-error : Bar k

foo : Bar _
foo = goal-type-error {_} {_}
