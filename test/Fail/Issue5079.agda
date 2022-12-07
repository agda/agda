{-# OPTIONS --erasure #-}

open import Agda.Builtin.Bool

data D : Set where
  c : Bool → D

f : @0 D → Bool
f (c true)  = true
f (c false) = false
