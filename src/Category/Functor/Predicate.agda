------------------------------------------------------------------------
-- The Agda standard library
--
-- Functors on indexed sets (predicates)
------------------------------------------------------------------------

-- Note that currently the functor laws are not included here.

module Category.Functor.Predicate where

open import Function
open import Level
open import Relation.Unary
open import Relation.Unary.PredicateTransformer using (PT)

record RawPFunctor {i j ℓ₁ ℓ₂} {I : Set i} {J : Set j}
                   (F : PT I J ℓ₁ ℓ₂) : Set (i ⊔ j ⊔ suc ℓ₁ ⊔ suc ℓ₂)
                   where
  infixl 4 _<$>_ _<$_

  field
    _<$>_ : ∀ {P Q} → P ⊆ Q → F P ⊆ F Q

  _<$_ : ∀ {P Q} → (∀ {i} → P i) → F Q ⊆ F P
  x <$ y = const x <$> y
