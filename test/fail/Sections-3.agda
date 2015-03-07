data D : Set where
  c_c_ : D → D

test : D → D
test c x c_ = x
