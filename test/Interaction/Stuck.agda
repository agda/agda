module Stuck where

postulate
  I   : Set
  i j : I

data D : I → I → Set where
  d : D i i
  e : D j j

f : ∀ {x} → D i x → Set₁
f p = {!!}
