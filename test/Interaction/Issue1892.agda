
data D : Set where
  d : D

foo : D
foo = {!!}
-- C-c C-r gives me a weird-looking '0'
