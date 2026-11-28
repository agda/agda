-- Size subtyping permits a constructor argument whose type has a different head from
-- its declared domain.  Such a constructor must remain available for disambiguation by inversion.

{-# OPTIONS --sized-types #-}

module ConstructorDisambiguationByInversion-SizedTypes where

open import Agda.Builtin.Bool using (Bool ; false ; true)
open import Agda.Builtin.Equality using (_≡_ ; refl)
open import Agda.Builtin.Size using (Size ; Size<_ ; ∞)

data A : Set where
  c : Size → A

data E : Set where
  c : Size< ∞ → E

data F : Set where
  c : Size< ∞ → F

-- Qualifying `A.c` checks that an argument of type `Size< i` is accepted at
-- type `Size` independently of constructor disambiguation in the two tests below.
qualified : (i : Size) → Size< i → A
qualified i x = A.c x

-- The argument-type comparison retains `E.c` and `F.c` and discards `A.c`,
-- although `Size< i` is a subtype of `Size`.  Only `A.c` has a target returned
-- by `El`, so inversion must consider the original candidates.  There is
-- deliberately no later equality to help Agda infer the index in `inferredIndex`.
module OriginalCandidates where
  El : Bool → Set
  El false = A
  El true  = Bool

  index : ∀ {i} → El i → Bool
  index {i} _ = i

  inferredIndex : (i : Size) → Size< i → Bool
  inferredIndex i x = index (c x)  -- Only `A.c` has a possible result type.

-- The argument-type comparison retains `E.c` and `F.c`, and inversion permits
-- `A.c` and `E.c`.  Taking the intersection would commit to `E.c` before
-- checking `refl` fixes the index to `false`.  Agda must postpone the choice
-- so it can accept the required `A.c x` by size subtyping.
module Intersection where
  El : Bool → Set
  El false = A
  El true  = E

  select : ∀ {b} → El b → b ≡ false → A
  select x refl = x

  test : (i : Size) → Size< i → A
  test i x = select (c x) refl  -- After postponement, the required constructor is `A.c`.

  computed : (i : Size) (x : Size< i) → test i x ≡ A.c x
  computed i x = refl
