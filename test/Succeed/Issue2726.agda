
module _ (A : Set) where

record R : Set where
  data D : Set where

open R (record {})

F : D → Set₃
F _ with Set₁
F _ | _ = Set₂
