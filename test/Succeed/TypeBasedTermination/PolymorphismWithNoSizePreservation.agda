-- --no-size-preservation enables type-based termiantion on its own
{-# OPTIONS --size-preservation --no-syntax-based-termination #-}
module TypeBasedTermination.PolymorphismWithNoSizePreservation where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

apply : {A B : Set} → (A → B) → A → B
apply f x = f x

add : Nat → Nat → Nat
add zero    y = y
add (suc x) y = suc (apply add x y)

add' : Nat → Nat → Nat
add' zero    y = y
add' (suc x) y = suc (apply (add' x) y)
