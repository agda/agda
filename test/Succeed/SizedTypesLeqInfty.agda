-- {-# OPTIONS --sized-types #-} Option obsolete since 2014-04-12.

module SizedTypesLeqInfty where

open import Common.Size
data Nat : {size : Size} -> Set where
  zero : {size : Size} -> Nat {↑ size}
  suc  : {size : Size} -> Nat {size} -> Nat {↑ size}

weak : {i : Size} -> Nat {i} -> Nat {∞}
weak x = x
