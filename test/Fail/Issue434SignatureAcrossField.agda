module Issue434SignatureAcrossField where

-- This could be reordered, but the inferred mutual block still crosses a field.
record R (A : Set) : Set where
  identity : A → A
  field a : A
  identity x = x
