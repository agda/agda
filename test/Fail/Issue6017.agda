{-# OPTIONS --cubical --no-double-check  #-}

module Issue6017 where

open import Agda.Primitive renaming (Set to Type)
open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical
  renaming ( primINeg       to infix  30 ~_   -- I → I
           ; primIMin       to infixr 20 _∧_  -- I → I → I
           ; primIMax       to infixr 20 _∨_  -- I → I → I
           ; primComp       to comp           -- for printing the error
           ; primHComp      to hcomp
           )

_∙_ : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(p ∙ q) i = hcomp (λ { j (i = i0) → p i0 ; j (i = i1) → q j }) (p i)

refl : ∀ {ℓ} {A : Type ℓ} (x : A) → x ≡ x
refl x i = x

data T : Type where
  base : T
  p    : base ≡ base
  surf : p ∙ p ≡ p

f : (x : T) → x ≡ x
f base       = refl base
f (p i)      = refl (p i)
f (surf i j) = refl (surf i j)
