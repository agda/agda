-- Lawrence, 2023-06-19, issue #6660

open import Agda.Builtin.Nat

record Pair (A B : Set) : Set where
  inductive
  constructor _,_
  field fst : A
        snd : B
open Pair

{-# INLINE _,_ #-}  -- expected to succeed

flip : ∀{A B} → Pair A B → Pair B A
flip p = snd p , fst p
