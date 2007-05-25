
module Elem where

open import Prelude
open import Star

Elem : {X : Set}(R : Rel X) -> Rel X
Elem R x y = Star (LeqBool [×] R) (false , x) (true , y)
