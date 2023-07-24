-- Andreas, Lawrence, 2023-06-12 issue #6660:
-- inline constructors to pass guardedness check

{-# OPTIONS --exact-split #-}
{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat

record Stream (A : Set) : Set where
  coinductive; pattern; constructor _∷_  -- Gives a warning for 'pattern' and then discards it.
  field head : A
        tail : Stream A
open Stream

{-# INLINE _∷_ #-}

nats : Nat → Stream Nat
nats n = n ∷ nats (1 + n)

map : {A B : Set} (f : A → B) → Stream A → Stream B
map f s = f (head s) ∷ map f (tail s)

-- Should give warnings about non-exact splitting
