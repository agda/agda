data ⊤ : Set where
  tt : ⊤

f : ⊤ → ⊤
f tt = tt

foo : ⊤ → ⊤
foo t with f t
... | x with f t
... | y with f t
... | z = {!z!}
