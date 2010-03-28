
module Issue249 where

postulate
  A B : Set

module A where
  X = A
  Y = B

open A renaming (X to C; Y to C)

-- open A using (X) renaming (Y to X)
