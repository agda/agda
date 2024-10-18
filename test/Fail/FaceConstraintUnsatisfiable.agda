open import Agda.Primitive.Cubical

data S : Set where
  base : S

foo : Partial i0 S
foo (i0 = i1) = base
