
module _ where

record ⊤ : Set where
  instance constructor tt

f : {{u : ⊤}} → ⊤
f = _

foo : (x : ⊤) → ⊤
foo x = f
