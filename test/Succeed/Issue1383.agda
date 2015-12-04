{-# OPTIONS --exact-split #-}
module Issue1383 where

data Bool : Set where
  true false : Bool

xor : Bool → Bool → Bool
xor = \ { true  true  -> false ;
          false false -> false ;
          {-# CATCHALL #-}
          _     _     -> true  }
