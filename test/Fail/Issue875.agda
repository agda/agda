
postulate
  A : Set
  P : ..(_ : A) → Set
  f : {x : A} → P x

g : ..(x : A) → P x
g x = f
