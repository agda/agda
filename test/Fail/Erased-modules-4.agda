module Erased-modules-4 where

module @0 M (@0 A : Set) where

  B : Set
  B = A

-- Everything in the module N is erased.

H : @0 Set → Set
H A = let module @0 N = M A in N.B
