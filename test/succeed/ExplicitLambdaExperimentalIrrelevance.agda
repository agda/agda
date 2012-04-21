{-# OPTIONS --experimental-irrelevance #-}
module ExplicitLambdaExperimentalIrrelevance where

postulate
  A : Set
  T : ..(x : A) -> Set  -- shape irrelevant type

test : .(a : A) -> T a -> Set
test a = λ (x : T a) -> A
-- this should type check and not complain about irrelevance of a


