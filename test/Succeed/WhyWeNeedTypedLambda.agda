{- 2010-09-28 Andreas, example from Alan Jeffery, see Issue 336 -}

-- {-# OPTIONS --profile=all -v tc.term.lambda:5 #-}

module WhyWeNeedTypedLambda where

data Bool : Set where
  true false : Bool

F : Bool -> Set
F true  = Bool -> Bool
F false = Bool

bool : {b : Bool} -> F b -> Bool
bool {b} _ = b

{-
-- untyped lambda leaves some yellow
-- the problem  \ x -> x : F ?b  is postponed
bla : Bool
bla = bool (\ x -> x)
-}

-- typed lambda succeeds
-- \ (x : _) -> x infers as ?X -> ?X, yielding constraint F ?b = ?X -> ?X
bla' : Bool
bla' = bool (\ (x : _) -> x)

testBinLam : Set → Set → Set
testBinLam = λ (x y : Set) → x
