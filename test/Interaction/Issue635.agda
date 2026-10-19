-- {-# OPTIONS -v interaction.case:10 -v tc.cover:40 #-}
module Issue635 where

record Pointed : Set₁ where
  field
    Carrier : Set
    empty : Carrier
    equal : Carrier → Carrier → Set

record PointedMorphism (M₁ M₂ : Pointed) : Set where
  constructor morph
  module M₁ = Pointed M₁
  module M₂ = Pointed M₂
  field
    f : M₁.Carrier → M₂.Carrier
    .identity : M₂.equal (f M₁.empty) M₂.empty

g : ∀ (M₁ M₂ : Pointed) → PointedMorphism M₁ M₂ → PointedMorphism M₁ M₂
g M₁ M₂ (morph f identity) = morph f identity

f : ∀ {M₁ M₂ : Pointed} → PointedMorphism M₁ M₂ → PointedMorphism M₁ M₂
f x = {!x!}

{- WAS:
case splitting on x in that hole produces this monstrosity:

f {.Splitting.recCon-NOT-PRINTED Carrier empty times equal} {.Splitting.recCon-NOT-PRINTED Carrier₁ empty₁ times₁ equal₁} (morph f identity) = ?
-}

-- Andreas, 2013-03-21
-- NOW: case splitting on x yields pattern (morph f identity)
