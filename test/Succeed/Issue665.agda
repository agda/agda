module Issue665 where

postulate
  A : Set

record I : Set where
  constructor i
  field
    f : A

data Wrap : (j : I) → Set where
  con : ∀ {j} → Wrap j

postulate
  C : Set
  anything : C

works1 : ∀ {X} -> Wrap X -> C
works1 (con {i _}) with anything
... | z = z

works2 : ∀ {X} -> Wrap X -> C
works2 (con {_}) with anything
... | z = z

bugged : ∀ {X} -> Wrap X -> C
bugged con with anything
... | z = z
