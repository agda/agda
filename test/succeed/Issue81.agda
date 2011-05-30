-- {-# OPTIONS -v tc.lhs.unify:50 #-}
module Issue81 where

data ⊥ : Set where

data D : Set where
  d : D
  c : D

data E : Set where
  e : E

⌜_⌝ : E -> D
⌜ e ⌝ = c

data R : D -> E -> Set where
  Val : (v : E) -> R ⌜ v ⌝ v

foo : R d e -> ⊥
foo ()

