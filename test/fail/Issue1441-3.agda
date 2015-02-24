-- Andreas, 2015-02-24

data Wrap (A : Set) : Set where
  wrap : A → Wrap A

data D : Set → Set1 where
  c : (A : Set) → D (Wrap A)

test : (A : Set) → D A → Set
test .(Wrap A) (c A) = A

-- this should crash Epic as long as A is considered forced in constructor c

-- should succeed now
