module Issue335 where

postulate
  A : Set
  k : (.A -> Set) -> A

bla = k (\ .(x : A) -> A)
-- syntax for irrelevant typed lambda now exists