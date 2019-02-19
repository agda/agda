{-# OPTIONS --safe --no-sized-types #-}

open import Agda.Builtin.Size

record Stream (A : Set) (i : Size) : Set where
  coinductive
  field
    head : A
    tail : {j : Size< i} → Stream A j

open Stream

destroy-guardedness : ∀ {A i} → Stream A i → Stream A i
destroy-guardedness xs .head = xs .head
destroy-guardedness xs .tail = xs .tail

repeat : ∀ {A i} → A → Stream A i
repeat x .head = x
repeat x .tail = destroy-guardedness (repeat x)
