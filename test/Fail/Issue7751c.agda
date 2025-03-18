{-# OPTIONS --safe #-}
module Issue7751c where

data ⊥ : Set where

module M (X : Set) where
  data ¬X : Set where
    neg : (X → ⊥) → ¬X

Bad : Set
open M Bad
Bad = ¬X

bad : Bad → ⊥
bad (neg f) = f (neg f)

oops : ⊥
oops = bad (neg bad)
