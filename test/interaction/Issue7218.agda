module Issue7218 where

data ⊤ : Set where
  tt : ⊤

opaque
  f : ⊤ → ⊤
  f = {! !}
