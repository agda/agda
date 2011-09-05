-- Sometimes we can't infer a record type

module InferRecordTypes-2 where

record R : Set₁ where
  field
    x₁ : Set
    x₂ : Set

bad = record { x₃ = Set }