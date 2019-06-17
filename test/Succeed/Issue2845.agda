module Issue2845 where

open import Agda.Builtin.Nat
open import Agda.Primitive.Cubical
open import Agda.Builtin.Equality

Ex1 : Nat
Ex1 = primComp (λ i → Nat) (λ i → isOneEmpty) zero

test1 : Ex1 ≡ zero
test1 = refl

Ex2 : (i : I) → Nat
Ex2 i = primComp (λ i → Nat) (λ { _ (i = i1) → zero}) zero

test2 : ∀ i → Ex2 i ≡ zero
test2 i = refl

Ex3 : (i : I) (p : I → Nat) → Nat
Ex3 i p = primComp (λ i → Nat) (λ { k (i = i1) → suc (p k)}) (suc (p i0))

test3 : ∀ i p → Ex3 i p ≡ suc _
test3 i p = refl
