{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Nat

record Stream (A : Set) : Set where
  coinductive; constructor _∷_
  field head : A
        tail : Stream A
open Stream

{-# INLINE _∷_ #-}

nats : Nat → Stream Nat
nats n = n ∷ nats (1 + n)

map : {A B : Set} (f : A → B) → Stream A → Stream B
map f s = f (head s) ∷ map f (tail s)
