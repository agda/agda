{-# OPTIONS --sized-types #-}

module SizedTypesFunctionFromSuccSize where

open import Common.Size

data Nat : {size : Size} → Set where
  zero : {size : Size} → Nat {↑ size}
  suc  : {size : Size} → Nat {size} → Nat {↑ size}

bad : {i : Size} → Nat {↑ i} → Set
bad zero    = bad zero
bad (suc x) = Nat

