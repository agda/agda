open import Agda.Primitive.Cubical renaming (primIMax to _∨_)

data S : Set where
  base : S

foo : ∀ (i j : I) → Partial (i ∨ j) S
foo i j (i ∨ j = i1) = base
