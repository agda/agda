
module Issue448 where

postulate
 Unit : Set
 unit : Unit
 D    : Set → Set
 d    : (A : Set) → A → D A

record R : Set₁ where
 field F : Set

r : _
r = record { F = Unit }

postulate
 D′ : R.F r → D (R.F r) → Set
 d′ : ∀ f τ → D′ f (d _ τ)

data D″ (f : Unit) : D′ f (d Unit unit) → Set where
  d″ : ∀ (x : Unit) → D″ _ (d′ f unit)

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/MetaVars.hs:583
