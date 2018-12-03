module _ where

module M (A : _) where

  y = Set -- type of A is solved if this is removed

  x : Set
  x = A

-- WAS: yellow on type of A
-- SHOULD: succeed
