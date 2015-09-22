
data D : Set → Set1 where
  c : (A B : Set) → D (A → B)

test : (X : Set) → D X → Set
test .(A → B) (c A B) = A

-- this should crash Epic as long as A is considered forced in constructor c
