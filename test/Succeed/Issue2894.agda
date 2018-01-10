
record ⊤ : Set where
  no-eta-equality
  constructor tt

data D : ⊤ → Set where
  d : (x : ⊤) → D x

test : (g : D tt) → Set
test (d tt) = ⊤
