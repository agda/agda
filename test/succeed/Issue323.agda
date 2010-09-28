-- {-# OPTIONS -v tc.meta:20 #-}
-- Agdalist 2010-09-24 David Leduc
module Issue323 where

data Sigma (A : Set)(B : A -> Set) : Set where
  _,_ : (a : A) -> B a -> Sigma A B

data Trivial {A : Set}(a : A) : Set where
  trivial : Trivial a 

lemma : (A : Set)(x y : A) -> Trivial (x , y)
lemma A x y = trivial