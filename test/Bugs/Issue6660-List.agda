-- Lawrence, 2023-06-19, issue #6660

open import Agda.Builtin.Nat

record List (A : Set) : Set where
  inductive; constructor _∷_
  field head : A
        tail : List A
open List

{-# INLINE _∷_ #-}

map : {A B : Set} (f : A → B) → List A → List B
map f s = f (head s) ∷ map f (tail s)
