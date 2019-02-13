-- {-# OPTIONS --cubical -vtc.lhs.split.partial:20 #-}
{-# OPTIONS --cubical #-}
module _ where
open import Agda.Primitive.Cubical
open import Agda.Builtin.Equality

postulate
  X : Set
  P : I → Set
  p : P i1

module Test (A : Set) (i : I) (B : Set) where

  j = i
  R = P j
  module Z (r s : A) where
    a0 : I → Partial j R
    a0 k with k
    ... | _ = \ { (j = i1) → p }

  a : Partial j R
  a (j = i1) = p

  refining : ∀ (x y : A) → x ≡ y → A → Partial j R
  refining x y refl = \ { _ (j = i1) → p }

  refining-dot : ∀ (x y : A) → x ≡ y → A → Partial j R
  refining-dot x .x refl = \ { _ (j = i1) → p }

  refining-dot2 : ∀ (x y : A) → x ≡ y → A → Partial j R
  refining-dot2 x .x refl z = \ { (i = i1) → p }

  refining-cxt : A ≡ X → Partial j R
  refining-cxt refl = \ { (j = i1) → p }

  refining-cxt2 : B ≡ X → Partial j R
  refining-cxt2 refl = \ { (j = i1) → p }
