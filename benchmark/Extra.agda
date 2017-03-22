module Extra where

open import Prelude


fromTo : Nat -> List Nat
fromTo n = f n
  where
    f : Nat -> List Nat
    f 0 = []
    f (suc i) = n - i ∷ f i

downFrom : Nat -> List Nat
downFrom 0 = []
downFrom (suc n) = (suc n) ∷ downFrom n

fromTo' : Nat -> List Nat
fromTo' = f []
  where
    f : List Nat -> Nat -> List Nat
    f xs 0 = xs
    f xs (suc x) = seq xs (f ( suc x ∷ xs ) x)

downFrom' : Nat -> List Nat
downFrom' n = f [] n
  where
    f : List Nat -> Nat -> List Nat
    f xs 0 = xs
    f xs (suc x) = seq xs (f ((n - x) ∷ xs) x)

blumblumshub : Nat -> (m : Nat) -> {{ nz : NonZero m }} -> Nat
blumblumshub xn M = natMod M (xn ^ 2)

downFromBbs' : Nat -> Nat -> List Nat
downFromBbs' seed = f seed []
  where
  f : Nat -> List Nat -> Nat -> List Nat
  f _ acc 0       = acc
  f x acc (suc l) = seq acc $ f (blumblumshub x M) ( x ∷ acc ) l
    where
      M M17 M31 : Nat
      M           = M17 * M31
      M17         = 2971
      M31         = 4111

fromToBbs : Nat -> Nat -> List Nat
fromToBbs _ 0 = []
fromToBbs xi (suc n) = xi ∷ fromToBbs (blumblumshub xi m) n
  where
    p = 2971
    q = 4111
    m = p * q
