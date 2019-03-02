-- Andreas, 2019-03-02, issue #3601 reported by 3abc

{-# OPTIONS --cubical --safe #-}

open import Agda.Primitive.Cubical renaming
  (primINeg to ~_; primIMin to _∧_; primTransp to transp)

open import Agda.Builtin.Cubical.Path

module _ (A : Set) (x y z t : A) (f : y ≡ z) (g : y ≡ x) (h : z ≡ t) where

  test : PathP (λ i → g i ≡ h i) f (transp (λ i → g i ≡ h i) i0 f)
  test k i = transp (λ i → g (i ∧ k) ≡ h (i ∧ k)) (~ k) f i

-- Should pass.
-- Problem was: Agda did not accept overapplied primTransp
