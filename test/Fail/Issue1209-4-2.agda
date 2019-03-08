-- Showing that destroy-guardedness in Issue1209-4 indeed does
-- destroy guardedness

{-# OPTIONS --safe --guardedness --no-sized-types #-}

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream

destroy-guardedness : ∀ {A} → Stream A → Stream A
destroy-guardedness xs .head = xs .head
destroy-guardedness xs .tail = xs .tail

repeat : ∀ {A} → A → Stream A
repeat x .head = x
repeat x .tail = destroy-guardedness (repeat x)
