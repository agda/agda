-- Record projections should be positive in their argument
module Issue602-2 where

record A : Set₁ where
  constructor mkA
  field
    f : Set

unA : A → Set
unA (mkA x) = x

data B (a : A) : Set where
  mkB : unA a → B a

data D : Set where
  d : B (mkA D) → D
