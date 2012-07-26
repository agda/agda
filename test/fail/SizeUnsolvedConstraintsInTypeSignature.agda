{-# OPTIONS --sized-types #-}
-- {-# OPTIONS -v tc.size.solve:20 -v tc.decl.ax:10 #-}
module SizeUnsolvedConstraintsInTypeSignature where

open import Common.Size

data Nat : (i : Size) -> Set where
  Z : {i : Size} -> Nat (↑ i)
  S : {i : Size} -> Nat i → Nat (↑ i)

one1 : (i : Size) → Nat (↑ (↑ i))
one1 i = S Z

one2 : (i : Size) → Nat (↑ (↑ (↑ i)))
one2 i = S Z

postulate
  _≡_   : {A : Set} → A → A → Set
  works : (i : Size) → one2 i ≡ one1 i

  bug   : (i : Size) → one1 i ≡ one2 i
  -- bug caused an interal error due to absense of range info
  -- should not print a proper error message (or better, work!)

