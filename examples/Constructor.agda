data N : Set where
  z : N
  s : N -> N

f : (N -> N) -> N
f g = g z

one = f s
