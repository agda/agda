module RecordUpdateSyntax where

data ⊤ : Set where
  tt : ⊤

record R : Set where
  field
    a b : ⊤

test : R
test = record {!!} { a = tt }
