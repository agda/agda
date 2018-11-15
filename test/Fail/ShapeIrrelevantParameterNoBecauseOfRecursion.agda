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

-- Jesper, 2017-09-14: I think the definition of D is fine, but the definition
-- of cast below should fail since `D a` and `D b` are different types.

-- Jesper, 2018-11-15: I disagree with Jesper!2017, D should be rejected.

fromD : {b : Bool} → D b → True b
fromD (c p) = p

cast : .(a b : Bool) → D a → D b
cast _ _ x = x

bot : ⊥
bot = fromD (cast true false (c _))
