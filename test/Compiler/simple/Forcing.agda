module Forcing where

open import Common.IO
open import Common.Unit
open import Lib.Vec
open import Common.Nat

len : {A : Set}{n : Nat} → Vec A n → Nat
len {A} .{zero}  []             = zero
len {A} .{suc n} (_∷_ {n} x xs) = suc n

len2 : {A : Set}{n : Nat} → Vec A n → Nat
len2 [] = 0
len2 (_∷_ {n} x xs) = suc (len2 {n = n} xs)

len3 : {A : Set}{n : Nat} → Vec A n → Nat
len3 {n = zero}  []              = zero
len3 {n = suc n} (_∷_ .{n} x xs) = suc n

len4 : {A : Set}{n : Nat} → Vec A n → Nat
len4 []                 = zero
len4 (_∷_ {zero}  x xs) = suc zero
len4 (_∷_ {suc n} x xs) = suc (suc n)

main : IO Unit
main =
    printNat (len  l1) ,,
    printNat (len  l2) ,,
    printNat (len  l3) ,,

    printNat (len2 l1) ,,
    printNat (len2 l2) ,,
    printNat (len2 l3) ,,

    printNat (len3 l1) ,,
    printNat (len3 l2) ,,
    printNat (len3 l3) ,,

    printNat (len4 l1) ,,
    printNat (len4 l2) ,,
    printNat (len4 l3) ,,

    return unit
  where l1 = "a" ∷ ("b" ∷ ("c" ∷ []))
        l2 = 1 ∷ (2 ∷ (3 ∷ (4 ∷ (5 ∷ []))))
        l3 : Vec Nat zero
        l3 = []
