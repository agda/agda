-- {-# OPTIONS -v tc.meta:20 #-}
module UnifyWithIrrelevantArgument where

data _≡_ {A : Set}(a : A) : A -> Set where
  refl : a ≡ a

fail : (A : Set) ->
       let X : .A -> A
           X = _
       in  (x : A) -> X x ≡ x
fail A x = refl
-- error: X cannot depend on its first argument
