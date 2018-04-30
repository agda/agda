
data C : Set₁ where
  c : Set → C

data D : Set where
  d : D

F : C → {y : D} → C → Set₁
F z (c _) = G d
  module M where
  G : D → Set₁
  G _ = Set

fail : Set
fail = M.G
