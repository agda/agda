{-# OPTIONS --experimental-irrelevance #-}
module ShapeIrrelevantParameterNoBecauseOfRecursion where

data ⊥ : Set where
record ⊤ : Set where

data Bool : Set where
  true false : Bool

True : Bool → Set
True false = ⊥
True true  = ⊤

data D ..(b : Bool) : Set where
  c : True b → D b  -- should fail

fromD : {b : Bool} → D b → True b
fromD (c p) = p

cast : .(a b : Bool) → D a → D b
cast _ _ x = x

bot : ⊥
bot = fromD (cast true false (c _))

