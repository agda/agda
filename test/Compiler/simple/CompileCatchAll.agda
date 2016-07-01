{-# OPTIONS -v treeless:20 #-}
module _ where

open import Common.Prelude

f : List Nat → List Nat → Nat
f _        []       = 0
f []       (y ∷ ys) = y
f (x ∷ xs) _        = x

main : IO Unit
main = printNat (f [] [])
    ,, printNat (f (1 ∷ []) [])
    ,, printNat (f [] (2 ∷ []))
    ,, printNat (f (3 ∷ []) (4 ∷ []))
