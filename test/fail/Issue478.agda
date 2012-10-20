-- {-# OPTIONS -v tc.display:100 #-}
module Issue478 where

record Ko (Q : Set) : Set₁ where
 field
  T : Set

module Bo (P : Set) (ko : Ko P) where
  open Ko ko

  err : T
  err = Set

{- The error message was:
  Set₁ !=< T P ko of type Set₂
  when checking that the expression Set has type T P ko

  We now get the desired error message:

  Set₁ !=< T of type Set₂
  when checking that the expression Set has type T

-}

