{-# OPTIONS --universe-polymorphism #-}

-- These examples should now go through with no unsolved metavariables.
-- They work since the conversion checker is a little less prone to
-- abort checking when there are constraints. In particular if the
-- constraints only affect the sorts of the things compared, then it keeps
-- going.
module Issue211 where

open import Common.Level

infixr 4 _,_
infixr 3 _×_

data _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  _,_ : A → B → A × B

data D₀ : Set₀ where
data D₁ : Set₁ where

-- Works:
ex₁ : (D₁ → D₁) × (D₁ → D₁)
ex₁ = ((λ d → d) , (λ d → d))

-- Works:

ex₂ : (D₀ → D₀) × (D₀ → D₀) × (D₀ → D₀)
ex₂ = ((λ d → d) , (λ d → d) , (λ d → d))

-- Works:

ex₃ : (D₁ → D₁) × (D₁ → D₁) × (D₁ → D₁)
ex₃ = ((λ d → d) , (λ (d : D₁) → d) , (λ (d : D₁) → d))

-- Does not work:

ex₄ : Level × (D₁ → D₁) × (D₁ → D₁)
ex₄ = lzero , (λ d → d) , (λ d → d)

ex₅ : (D₁ → D₁) × (D₁ → D₁) × (D₁ → D₁)
ex₅ = (λ (d : _) → d) , (λ (d : _) → d) , (λ (d : _) → d)

-- Does not work:

ex₆ : (D₁ → D₁) × (D₁ → D₁) × (D₁ → D₁)
ex₆ = (λ d → d) , (λ d → d) , (λ d → d)

-- As far as I can tell there is an easily found unique solution for
-- the unsolved meta-variables above. Why does not the unification
-- machinery find it? Are the meta-variables solved in the wrong
-- order?
