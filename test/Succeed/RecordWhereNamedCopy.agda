module RecordWhereNamedCopy where

record X : Set₁ where
  field
    x : Set
    y : Set

module Y (_ : Set₁) where postulate
  a : Set
  y : Set

_ : X
_ = record where
  open module Z = Y Set renaming (a to x) using (y)

_ : X
_ = record where
  module Z = Y Set renaming (a to x) using (y)
  open Z
