-- {-# OPTIONS -v tc.meta:20 #-}
-- Andreas, 2011-04-21
module PruneLHS where

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

data Bool : Set where true false : Bool

test : let X : Bool -> Bool -> Bool -> Bool
           X = _
       in (C : Set) ->
          (({x y : Bool} -> X x y x ≡ x) ->
           ({x y : Bool} -> X x x y ≡ x) -> C) -> C
test C k = k refl refl
-- by the first equation, X cannot depend its second argument
-- by the second equation, X cannot depend on its third argument
