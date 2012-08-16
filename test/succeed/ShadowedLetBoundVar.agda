-- issue 685
module ShadowedLetBoundVar where

import Common.Level

record Wrap {a}(A : Set a) : Set a where
  constructor wrap
  field wrapped : A

-- let is not recursive
works : Set → Set
works x = let x = x in x

fails : Set → Set
fails A = let wrap A = wrap A in A
-- works now

