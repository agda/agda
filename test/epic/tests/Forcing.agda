module tests.Forcing where

open import Prelude.IO
open import Prelude.Unit
open import Prelude.Vec
open import Prelude.Nat

len : {A : Set}{n : Nat} -> Vec A n -> Nat
len {A} .{Z}   []              = Z
len {A} .{S n} (_::_ {n} x xs) = S n


len2 : {A : Set}{n : Nat} -> Vec A n -> Nat
len2 [] = 0
len2 (_::_ {n} x xs) = S (len2 {n = n} xs)


len3 : {A : Set}{n : Nat} -> Vec A n -> Nat
len3 {n = Z}   []               = Z
len3 {n = S n} (_::_ .{n} x xs) = S n


len4 : {A : Set}{n : Nat} -> Vec A n -> Nat
len4 []               = Z
len4 (_::_ {Z} x xs) = S Z
len4 (_::_ {S n} x xs) = S (S n)



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
  where l1 = "a" :: "b" :: "c" :: []
        l2 = 1   :: 2   :: 3   :: 4 :: 5 :: []
        l3 : Vec Nat Z
        l3 = []