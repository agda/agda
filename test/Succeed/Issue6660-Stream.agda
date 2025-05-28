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

nats1 : Nat → Stream Nat
nats1 = λ n → n ∷ nats1 (1 + n)

id : {A : Set} → A → A
id = λ x → x
{-# INLINE id #-}

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
f ∘ g = λ x → f (g x)
{-# INLINE _∘_ #-}

_∷₁_ : {A B : Set} → (A → B) → (A → Stream B) → A → Stream B
{-# INLINE _∷₁_ #-}
h ∷₁ t = λ x → h x ∷ t x

nats2 : Nat → Stream Nat
nats2 = id ∷₁ (nats2 ∘ suc)

-- Should give warnings about non-exact splitting
