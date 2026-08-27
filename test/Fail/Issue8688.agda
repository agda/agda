-- Andreas, 2026-08-27, issue #8688
-- Report and test case by bdrisc-ant

-- Occurrence analysis in the positivity checker did not traverse into sorts,
-- so functions were falsely declared as NonVariant in level arguments.
-- This could be exploited to prove Type:Type.

{-# OPTIONS --safe #-}

-- {-# OPTIONS -v tc.pos:45 #-}
-- {-# OPTIONS -v tc.polarity:20 #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

data ⊥ : Set where

record LiftU {ℓ} (A : Set ℓ) : Setω where
  constructor liftU
  field low : A

-- This function was falsely declared NonVariant in the level argument.
F : Bool → Level → Setω
F true  l = LiftU (Set l)
F false l = LiftU (Set l)

cast : (b : Bool) (x y : Level) → F b x → F b y
cast b x y v = v

-- @cast@ should not be accepted, otherwise we can get Type:Type.

-- Expected error: [UnequalTerms]
-- The terms
--   x
-- and
--   y
-- are not equal at type Level
-- when checking that the expression v has type F b y

shrink : Set₁ → Set
shrink A = LiftU.low (cast true (lsuc lzero) lzero (liftU A))

data V : Set where
  sup : shrink (Σ Set (λ A → A → V)) → V

_∈_ : V → V → Set
x ∈ sup (A , f) = Σ A (λ a → f a ≡ x)

R : V
R = sup ((Σ V (λ x → x ∈ x → ⊥)) , fst)

out : ∀ {X} → X ∈ R → (X ∈ X → ⊥)
out ((Y , ny) , refl) = ny

R∉R : R ∈ R → ⊥
R∉R p = out p p

boom : ⊥
boom = R∉R ((R , R∉R) , refl)
