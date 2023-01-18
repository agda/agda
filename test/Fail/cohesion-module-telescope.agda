{-# OPTIONS --cohesion #-}

module _ where

data Unit : Set where
  tt : Unit

module M (continuous : Unit) where
  @♭ flat : Unit
  flat = tt

module N (continuous : Unit) where
  open M continuous public

wrong-signature : Unit → Unit
wrong-signature = N.flat
