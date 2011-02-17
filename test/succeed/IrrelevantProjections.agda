module IrrelevantProjections where

record [_] (A : Set) : Set where
  field
    .inflate : A

open [_] using (inflate)

.proj : ∀ {A} → [ A ] → A
proj x = inflate x
