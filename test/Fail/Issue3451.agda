-- Reported by nad, 2018-12-13.
-- The option --no-sized-types should turn off sized types
{-# OPTIONS --no-sized-types #-}

{-# BUILTIN SIZE   Size   #-}
{-# BUILTIN SIZELT Size<_ #-}

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
