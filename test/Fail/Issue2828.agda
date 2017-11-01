
module _ where

data ⊤ : Set where tt : ⊤

pattern id x = x

postulate
  X : Set

loops : X
loops = tt
