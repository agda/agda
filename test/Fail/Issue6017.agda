{-# OPTIONS --cubical --no-double-check  #-}

module Issue6017 where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
  renaming (primIMax to _∨_ ; primIMin to _∧_ ; primINeg to ~_ ; primComp to comp ; primHComp to hcomp)

_∙_ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(p ∙ q) i = hcomp (λ { j (i = i0) → p i0 ; j (i = i1) → q j }) (p i)

refl : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
refl x i = x

data T : Type where
  base : T
  p    : base ≡ base
  surf : p ∙ p ≡ p

f : (x : T) → x ≡ x
f base       = refl T.base
f (p i)      = refl (p i)
f (surf i j) = refl (surf i j)
