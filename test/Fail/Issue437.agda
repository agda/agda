record Unit : Set where
data Bool : Set where true false : Bool

F : Bool -> Set
F true  = Bool
F false = Unit

f : (b : Bool) -> F b
f true  = true
f false = record {}

-- this should give an error, but only gives yellow
test : Bool
test = f _ false
