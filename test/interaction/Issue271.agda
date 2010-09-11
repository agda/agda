module Issue271 where

data D (A : Set) : Set where
  d : D A → D A

f : {A : Set} → D A → D A
f x = d {!!}
