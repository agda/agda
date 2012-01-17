-- Andreas, 2012-01-17
-- {-# OPTIONS -v tc.proj.like:50 #-}
-- {-# OPTIONS -v tc.conv.atom:50 #-}
module Issue553c where

postulate 
  A : Set
  a : A

data Bool : Set where
  true false : Bool

data WrapBool (C : Set) : Set where
  wrap : Bool -> WrapBool C

-- a projection-like function (must not be constructor-headed!)
-- the dummy C is to make Agda accept f as projection like
f : {C : Set} -> WrapBool C -> A
f (wrap true)  = a
f (wrap false) = a

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

-- it is important that f does not reduce, in order to enter compareAtom
test : (b : Bool) -> f {C = A} (wrap b) ≡ f (wrap b)
test b = refl
-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/Conversion.hs:335

-- the problem is fixed now, since f is no longer projection-like 
-- because of deep matching