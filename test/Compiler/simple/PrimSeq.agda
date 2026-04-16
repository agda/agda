
module _ where

open import Agda.Builtin.Nat using (mod-helper)
open import Common.Prelude
open import Common.Equality

_mod_ : Nat → Nat → Nat
n mod zero  = 0
n mod suc m = mod-helper 0 m n m

{-# INLINE _mod_ #-}

primitive
  primForce      : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) → (∀ x → B x) → B x
  primForceLemma : ∀ {a b} {A : Set a} {B : A → Set b} (x : A) (f : ∀ x → B x) → primForce x f ≡ f x

force      = primForce
forceLemma = primForceLemma

infixr 0 _$!_
_$!_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $! x = force x f

-- Memory leak without proper seq --

pow′ : Nat → Nat → Nat
pow′ zero    acc = acc
pow′ (suc n) acc = pow′ n $! (acc + acc) mod 234576373

pow : Nat → Nat
pow n = pow′ n 1

main : IO Unit
main = printNat (pow 5000000)
