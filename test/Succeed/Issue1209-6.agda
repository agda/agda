-- The option --guardedness turns off sized types, but this can be
-- overridden using --sized-types.

{-# OPTIONS --guardedness --sized-types #-}

open import Agda.Builtin.Size

record Stream (A : Set) (i : Size) : Set where
  coinductive
  field
    head : A
    tail : {j : Size< i} → Stream A j

open Stream

postulate
  destroy-guardedness : {A : Set} → A → A

repeat : ∀ {A i} → A → Stream A i
repeat x .head = x
repeat x .tail = destroy-guardedness (repeat x)
