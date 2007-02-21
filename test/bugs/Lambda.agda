
-- forcePi should be allowed to generate constraints

module Lambda where

data Bool : Set where
  true : Bool
  false : Bool

T : Bool -> Set
T true  = Bool -> Bool
T false = Bool

id : {x : Bool} -> T x -> T x
id y = y

f : Bool -> Bool
f = id (\x -> x)
