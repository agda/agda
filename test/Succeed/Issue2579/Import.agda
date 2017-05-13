module Issue2579.Import where

record Wrap A : Set where
  constructor wrap
  field wrapped : A
