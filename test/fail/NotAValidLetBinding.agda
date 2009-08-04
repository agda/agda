-- Let-definitions cannot pattern match (or be recursive). Use where for that.
module NotAValidLetBinding where

data N : Set where
  z : N
  s : N -> N

bad = let pred : N -> N
          pred z     = z
          pred (s n) = n
      in pred (s (s z))
