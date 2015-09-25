-- Check that F is in not in scope at the top-level (but in the hole).
module _ where

private
  postulate F : Set → Set

Hole : Set
Hole = {!!}
