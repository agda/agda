-- Andreas, 2012-01-13
module Issue555b where

data Empty : Set where
record Unit : Set where
  constructor tt

-- Do we want to allow this?
data Exp (A : Set) : Set1
data Exp where -- ? needs to report that too few parameters are given
  var : Exp Empty
  app : {A B : Set} → Exp (A → B) → Exp A → Exp B

-- Basically, A is first declared as a parameter, but later,
-- in the definition, it is turned into an index.

bla : {A : Set} → Exp A → Unit
bla var = tt
bla (app f a) = bla f 

