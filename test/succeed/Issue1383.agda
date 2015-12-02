{-# OPTIONS --exact-split #-}
module Issue1383 where

data Bool : Set where
  true false : Bool

data Void : Set where

data _≡_ {A : Set}(x : A) : A -> Set where
  refl : x ≡ x

xor : Bool → Bool → Bool
xor = \ { true  true  -> false ;
          false false -> false ;
          {-# CATCHALL #-}
          _     _     -> true  }
