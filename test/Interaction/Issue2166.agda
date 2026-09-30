-- {-# OPTIONS -v tc.cover.split.con:100 #-}

{-# OPTIONS --show-implicit #-}

data D : Set where
  d : {x : D} → D

f : D → Set
f y = {!!}
