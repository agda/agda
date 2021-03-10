{-# OPTIONS --experimental-irrelevance #-}
-- {-# OPTIONS -v tc:10 #-}

module ExplicitLambdaExperimentalIrrelevance where

postulate
  A : Set
  T : ..A -> Set  -- shape irrelevant type
      -- issue #4310: parse ..A -> B

test : .(a : A) -> T a -> Set
test a = λ (x : T a) -> A
-- this should type check and not complain about irrelevance of a

module M .(a : A) where

  -- should also work with module parameter
  test1 : T a -> Set
  test1 = λ (x : T a) -> A
