{-# OPTIONS --rewriting #-}
module _ where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data D (A : Set) : Set₁ where
  c₁ : D A
  c₂ : Set → D A

f : {A : Set} → D A → Set
f c₁ = Bool
f (c₂ X) = X

postulate
  rew : (A : Set) → c₁ {A} ≡ c₂ A

-- This rewrite rule is rejected because the A on the lhs of the rule
-- only appears in a parameter position, but parameters are erased.
-- Reconstructing the parameter would only be possible if we had
-- access to the type during reduction, but we don't.
{-# REWRITE rew #-}

boom : f {Bool} c₁ ≡ Bool
boom = refl
