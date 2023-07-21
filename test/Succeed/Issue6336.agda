{-# OPTIONS --cubical --safe --no-double-check #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical

-- Andreas Abel reported that this example is due to David Wärn.

id : (A : Set) → A → A
id _ x = x

data D : Set where
  point : D
  loop  : point ≡ id D point

-- The following example was taken from test/Fail/Issue6017.agda.

_∙_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(p ∙ q) i = primHComp
  (λ where
     j (i = i0) → p i0
     j (i = i1) → q j)
  (p i)

data T : Set where
  base : T
  p    : base ≡ base
  surf : p ∙ p ≡ p
