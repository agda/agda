module Issue205 where

data ⊥ : Set where

data D : Set₁ where
  d : (Set → Set) → D

_*_ : D → Set → Set
d F * A = F A

foo : (F : D) → F * ⊥
foo (d _) = ⊥
