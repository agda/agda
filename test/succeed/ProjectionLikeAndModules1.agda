-- {-# OPTIONS -v tc.proj.like:10 #-} {-# OPTIONS -v tc.conv:10 #-}
import Common.Level

module ProjectionLikeAndModules1 (A : Set) (a : A) where

record ⊤ : Set where
  constructor tt

data Wrap (W : Set) : Set where
  wrap : W → Wrap W

data Bool : Set where
  true false : Bool

-- `or' should be projection like in the module parameters
if : Bool → {B : Set} → B → B → B
if true  a b = a
if false a b = b

postulate
  u v : ⊤
  P : Wrap ⊤ -> Set

test : (y : Bool)
  -> P (if y (wrap u) (wrap tt))
  -> P (if y (wrap tt) (wrap v))
test y h = h

-- Error:
-- u != tt of type Set
-- when checking that the expression h has type
-- P (if y (wrap tt) (wrap v))
