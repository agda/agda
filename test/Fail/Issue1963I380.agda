-- Andreas, 2016-07-21
-- Test case to ensure postfix printing of projections.

{-# OPTIONS --postfix-projections #-}

open import Common.Product
open import Common.Equality

testProj : {A : Set}{B : A → Set}(y z : Σ A B) →
  let X : Σ A B
      X = _
  in X .proj₁ ≡ y .proj₁ → X .proj₂ ≡ z .proj₂
testProj y z = _ , _
