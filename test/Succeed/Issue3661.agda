{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-}
{-# OPTIONS -WnoInteractionMetaBoundaries #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path

module _ where


data D (A : Set) : Set where
  c    : D A
  step : ∀ (x : D A) → c ≡ x

data _~_ {A : Set} : (x y : D A) → Set

record _~′_ {A : Set} (x y : D A) : Set where
  coinductive
  field
    force : x ~ y
open _~′_

data _~_ {A} where
  c~    : ∀ {x y : D A} → c ~ c
  step~ : ∀ {x y} → (p : x ~′ y) → PathP (λ i → step x i ~ step y i) c~ (p .force)

foo : ∀ {A : Set} (x y : D A) → (x ~ y) → Set₁
foo _ _ (step~ _ _) = {!!}
foo _ _ c~ = {!!}
