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

blumblumshub : Nat -> (m : Nat) -> {{ nz : NonZero m }} -> Nat
blumblumshub xn M = natMod M (xn ^ 2)

downFromBbs : Nat -> Nat -> List Nat
downFromBbs seed = f seed []
  where
  f : Nat -> List Nat -> Nat -> List Nat
  f _ acc 0       = acc
  f x acc (suc l) = f (blumblumshub x M) ( x ∷ acc ) l
    where
      M M17 M31 : Nat
      M           = M17 * M31
      M17         = 2971
      M31         = 4111

