postulate
  C : Set
  anything : C

record I : Set where
  constructor c
  field
    f : C

data Wrap : (j : I) → Set where
  wrap : ∀ {j} → Wrap j

works1 : ∀ {j} → Wrap j → C
works1 {c ._} (wrap {j = c _}) with anything
... | z = z
