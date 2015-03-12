-- Andreas, 2015-03-12
-- Sizes should be irrelevant in terms, while they are relevant in types!

{-# OPTIONS --experimental-irrelevance #-}

open import Common.Size
open import Common.Equality

module IrrelevantSizes where

  -- Nat i is shape-irrelevant in i.

  data Nat ..(i : Size) : Set where
    zero : .(j : Size< i) → Nat i
    suc  : .(j : Size< i) → Nat j → Nat i

  add : .(i : Size) → Nat i → Nat ∞ → Nat ∞
  add i (zero j) y = y
  add i (suc j x) y = suc ∞ (add j x y)

  -- Proving this lemma is much easier with irrelevant sizes
  -- in constructors zero and suc

  plus0 : .(i : Size) (x : Nat i) → add ∞ x (zero ∞) ≡ x
  plus0 i (zero j) = refl                       -- Goal: zero ∞ = zero j
  plus0 i (suc j x) = cong (suc ∞) (plus0 j x)  -- Goal: suc ∞ (add j x (zero ∞)) ≡ suc j x

