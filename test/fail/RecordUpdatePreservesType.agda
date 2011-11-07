module RecordUpdatePreservesType where

data ⊤ : Set where
  tt : ⊤

record R : Set where
  field
    a : ⊤

record Q : Set where
  field
    a : ⊤

old : R
old = record { a = tt }

new : Q
new = record old { a = tt }
