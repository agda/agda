-- Andreas, 2012-09-07
module DataParameterPolarity where

data Bool : Set where
  true false : Bool

data ⊥ : Set where
record ⊤ : Set where

-- True uses its first argument.
True : Bool → Set
True true  = ⊤
True false = ⊥

-- Hence, D also uses its first argument.
-- A buggy polarity analysis may consider D as constant.
data D (b : Bool) : Set where
  c : True b → D b

d : {b : Bool} → D b → True b
d (c x) = x

-- This cast is fatal, possible if D is considered constant.
cast : (a b : Bool) → D a → D b
cast a b x = x

bot : ⊥
bot = d (cast true false (c _))
