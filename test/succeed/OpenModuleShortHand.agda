
module OpenModuleShortHand where

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

module List (Elem : Set) where

  data List : Set where
    []   : List
    _::_ : Elem -> List -> List

open List Nat

{- This means
open module _ = List Nat
-}

xs : List
xs = zero :: (suc zero :: [])
