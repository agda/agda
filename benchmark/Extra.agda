module Extra where

open import Prelude

fromTo : Nat -> List Nat
fromTo = f []
  where
    f : List Nat -> Nat -> List Nat
    f xs 0 = xs
    f xs (suc x) = f ( x ∷ xs ) x

downFrom : Nat -> List Nat
downFrom n = f [] n
  where
    f : List Nat -> Nat -> List Nat
    f xs 0 = xs
    f xs (suc x) = f ((n - x) ∷ xs) x
