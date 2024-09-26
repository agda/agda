-- Andreas, 2024-08-01
-- Trigger error ExpectedIntervalLiteral

{-# OPTIONS --cubical #-}

open import Agda.Builtin.Cubical.Path
open import Agda.Primitive.Cubical

postulate
  foo : I

_∙_ : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
(p ∙ q) i = primHComp
  (λ where
     j (i = i0) → p i0
     j (i = foo) → q j)
  (p i)

-- Expected error:
