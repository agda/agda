{-# OPTIONS --safe --no-guardedness #-}

record Stream (A : Set) : Set where
  coinductive
  field
    head : A
    tail : Stream A

open Stream

repeat : ∀ {A} → A → Stream A
repeat x .head = x
repeat x .tail = repeat x
