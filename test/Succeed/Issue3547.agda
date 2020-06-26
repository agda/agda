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

  refining : ∀ (x y : A) → x ≡ y → A → A
  refining x y refl = \ x -> x
    where
      prf : A → Partial j R
      prf = \ { _ (j = i1) → p }

  refining-dot : ∀ (x y : A) → x ≡ y → A → A
  refining-dot x .x refl = \ x -> x
    where
      prf : A → Partial j R
      prf = \ { _ (j = i1) → p }

  refining-dot2 : ∀ (x y : A) → x ≡ y → A → A
  refining-dot2 x .x refl z = z
    where
      prf : Partial j R
      prf = \ { (i = i1) → p }

  refining-cxt : A ≡ X → A → A
  refining-cxt refl = \ x -> x
     where
       prf : Partial j R
       prf = \ { (j = i1) → p }

  refining-cxt2 : B ≡ X → A → A
  refining-cxt2 refl = \ x → x
     where
       prf : Partial j R
       prf = \ { (j = i1) → p }
