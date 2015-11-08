{-# OPTIONS --show-implicit #-}
-- {-# OPTIONS -v tc.meta:20 #-}

module UnifyWithIrrelevantArgument where

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

data Bool : Set where true false : Bool

-- irrelevant arguments are ignored in unification
-- e.g. non linearity
test : let X : Bool -> .Bool -> Bool
           X = _
       in  (x : Bool) -> X x x ≡ x
test x = refl

-- e.g. non-pattern
tst1 : let X : Bool -> .Bool -> Bool
           X = _
       in  (x : Bool) -> X x true ≡ x
tst1 x = refl
