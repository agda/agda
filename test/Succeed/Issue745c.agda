
postulate
  U V : Set
  T   : V → Set
  H   : ∀ v → T v → Set
  f   : U → V

data D : Set where d : D

foo : (u : U) (t : T (f u)) (h : H (f u) t) → H (f u) t
foo u t h with f u | d
... | fu | x = h
