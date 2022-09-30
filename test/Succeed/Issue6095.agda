-- Andreas, 2022-09-30, issue #6095, raised by carlostome

data D : Set where
  c  : D

data E : Set where
  c' : E

pattern p = c

pattern p = c'

f : D → Set
f p = D

module _ where  -- This caused a "Multiple definitions of p" error

-- Should succeed.
