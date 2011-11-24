{-# OPTIONS --no-coverage-check #-}
module FlexibleFunArity where

data Bool : Set where true false : Bool

g : Bool -> Bool -> Bool
g true = \ x -> true
g false true  = false
g false false = true

T : Bool -> Set
T true  = Bool
T false = Bool -> Bool

f : (b : Bool) -> T b
f true = true
f false true  = false
f false false = true

{- checking clause 

  f false true

starts with 

  f (b : Bool) : T b

splits on b

  f true   -- no match, discard
  f false  -- matches

instantiate type

  f false : T false = Bool -> Bool

extend clause

  f false (y : Bool) : Bool

split on y

  f false true  -- matches
  f false false -- no match, discard

done
-}


{- coverage check starts with

  f (x : Bool)

splits on x

  f true   -- finds clause 1
  f false

NEW: remaing clauses have bigger arity, so expands to

  f false (y : Bool)

splits on y

  f false true  -- finds clause 2
  f false false -- finds clause 3

done
-}

