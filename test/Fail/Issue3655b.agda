{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Bool

postulate
  A : Set

F : Bool → Set
F true  = A
F false = A

data D {b : Bool} (x : F b) : Set where

variable
  b : Bool
  x : F b

postulate
  f : D x → (P : F b → Set) → P x
