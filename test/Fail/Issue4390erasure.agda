{-# OPTIONS --erasure #-}

open import Agda.Builtin.Equality

postulate
  X : Set
  rigid0 : ((@0 x : X) → X) → X

mutual
  H : ((@ω x : X) → X) → X
  H f = rigid0 _

  testω : (f : (@0 x : X) → X) → H (\ (@ω x) → f x) ≡ rigid0 (\ (@0 x) → f x)
  testω f = refl
