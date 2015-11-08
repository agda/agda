
module _ where

record ⊤ : Set where
  constructor tt

f : {{u : ⊤}} → ⊤
f = _

foo : (x : ⊤) → ⊤
foo x = f
