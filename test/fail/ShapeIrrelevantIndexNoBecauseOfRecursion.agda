{-# OPTIONS --experimental-irrelevance #-}
module ShapeIrrelevantIndexNoBecauseOfRecursion where

data ⊥ : Set where

record ⊤ : Set where
  constructor trivial

data Bool : Set where
  true false : Bool

True : Bool → Set
True false = ⊥
True true  = ⊤

data D : ..(b : Bool) → Set where
  c : {b : Bool} → True b → D b
-- because  of the irrelevant index,
-- D is in essence an existental type D : Set
-- with constructor c : {b : Bool} → True b → D

fromD : {b : Bool} → D b → True b
fromD (c p) = p -- should fail

cast : .(a b : Bool) → D a → D b
cast _ _ x = x

bot : ⊥
bot = fromD (cast true false (c trivial))
