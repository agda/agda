{-# OPTIONS --allow-unsolved-metas #-}

postulate
  A B : Set
  b : B

  f : {{B}} → Set

instance
  inst₁ : {{A}} → B
  inst₁ = b

  inst₂ : B
  inst₂ = b

test : Set
test = f
-- WAS: No instance of type A was found in scope.
-- when checking that the expression f has type Set

-- NOW: unsolved instance with 2 open candidates

