{-# OPTIONS --cubical #-}
module _ where

-- Test case by Ulf Norell, 16/09/2020

open import Agda.Primitive.Cubical    renaming (primIMin to _∧_)
open import Agda.Builtin.Cubical.Path using (_≡_)

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

record Pos : Set where
  constructor 1+_
  field unpos : Nat

open Pos

Pos→Nat : Pos → Nat
Pos→Nat (1+ n) = suc n

variable
  A : Set
  x : A

refl : x ≡ x
refl {x = x} i = x

id : Pos → Pos
id n = n

-- (i ∧ j) in the system caused a mishandling of de Bruijn indexes.
foo : (n : Pos) (i j : I) → Nat
foo n i j = primHComp
              (λ k → primPOr (i ∧ j)                (i ∧ j)
                             (λ _ → suc (n .unpos)) (λ _ → suc (n .unpos)))
              (suc (n .unpos))

-- The test triggers normalization to make sure the `primHComp` in
-- `foo` reduces properly.
                             --  v  foil syntactic equality check
test : ∀ n i j → foo n i j ≡ foo (id n) i j
test n i j = refl
