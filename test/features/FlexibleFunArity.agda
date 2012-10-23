-- {-# OPTIONS --no-coverage-check #-}
module FlexibleFunArity where

open import Common.Equality

data Bool : Set where true false : Bool

g : Bool -> Bool -> Bool
g false true  = false
g true = \ x -> true
g false false = true
-- g true false = false -- Unreachable clause

testg1 : ∀ {x} → g true x ≡ true
testg1 = refl

testg2 : g false true ≡ false
testg2 = refl

testg3 : g false false ≡ true
testg3 = refl


T : Bool -> Set
T true  = Bool
T false = Bool -> Bool

f : (b : Bool) -> T b
f false true  = false
f false false = true
f true = true

testf1 : f true ≡ true
testf1 = refl

testf2 : f false true ≡ false
testf2 = refl

testf3 : f false false ≡ true
testf3 = refl


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

