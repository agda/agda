-- Lawrence, 2023-06-19, issue #6660
-- Andreas, 2023-07-24, issue #6702

{-# OPTIONS --exact-split #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

record Pair (A B : Set) : Set where
  inductive
  constructor _,_
  field fst : A
        snd : B
open Pair

{-# INLINE _,_ #-}  -- expected to succeed without exact-split warning

flip : ∀{A B} → Pair A B → Pair B A
flip p = snd p , fst p

_ : ∀{A B} {p : Pair A B} → flip p ≡ (snd p , fst p)
_ = refl
