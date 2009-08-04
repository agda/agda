
-- The Berry majority function.

module Berry where

  data Bool : Set where
    F : Bool
    T : Bool

  maj : Bool -> Bool -> Bool -> Bool
  maj T T T = T
  maj T F x = x
  maj F x T = x
  maj x T F = x   -- doesn't hold definitionally
  maj F F F = F

  postulate
    z : Bool

