-- Andreas, 2011-04-21
module DontPruneLHS where

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

data Bool : Set where true false : Bool

test : let X : Bool -> Bool -> Bool -> Bool
           X = _
       in (C : Set) ->
          (({x y : Bool} -> X x y x ≡ x) ->
           ({x y : Bool} -> X x x y ≡ x) -> C) -> C
test C k = k refl refl
-- this should not be solved by unification
-- the first equation does NOT imply that X does not depend on its second argument
-- neither can anything be deduced from the second equation
