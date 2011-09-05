-- Sometimes we can't infer a record type

module InferRecordTypes-3 where

postulate A : Set

record R : Set₁ where
  field
    x₁ : Set
    x₂ : Set

record R′ : Set₁ where
  field
    x₁ : Set
    x₃ : Set

bad = record { x₂ =  A; x₃ = A }
