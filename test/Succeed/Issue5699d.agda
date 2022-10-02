{-# OPTIONS --allow-unsolved-metas #-}

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat

data D : Nat → Set where
  c : (n : Nat) → D n → D n

c' = c

macro
  m : Term → TC ⊤
  m a = do
     _ ← withReconstructed (getDefinition (quote c'))
     returnTC _

test : Term
test = m
