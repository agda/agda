-- The Agda primitives (preloaded).

{-# OPTIONS --without-K #-}

module Agda.Primitive where

------------------------------------------------------------------------
-- Universe levels
------------------------------------------------------------------------

infixl 6 _⊔_

-- Level is the first thing we need to define.
-- The other postulates can only be checked if built-in Level is known.

postulate
  Level : Set

-- MAlonzo compiles Level to (). This should be safe, because it is
-- not possible to pattern match on levels.

{-# COMPILE GHC Level = type () #-}
{-# BUILTIN LEVEL Level #-}

postulate
  lzero : Level
  lsuc  : (ℓ : Level) → Level
  _⊔_   : (ℓ₁ ℓ₂ : Level) → Level

{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

module CubicalPrimitives where
  {-# BUILTIN INTERVAL I    #-} -- I : Setω

  {-# BUILTIN IZERO    i0   #-}
  {-# BUILTIN IONE     i1   #-}

  infix 30 primINeg

  primitive
      primIMin : I → I → I
      primIMax : I → I → I
      primINeg : I → I

  {-# BUILTIN ISONE        IsOne #-} -- IsOne : I → Setω


  postulate
    itIsOne : IsOne i1
    IsOne1  : ∀ i j → IsOne i → IsOne (primIMax i j)
    IsOne2  : ∀ i j → IsOne j → IsOne (primIMax i j)

  {-# BUILTIN ITISONE      itIsOne  #-}
  {-# BUILTIN ISONE1       IsOne1   #-}
  {-# BUILTIN ISONE2       IsOne2   #-}
  {-# BUILTIN PARTIAL      Partial  #-}
  {-# BUILTIN PARTIALP     PartialP #-}

  postulate
    isOneEmpty : ∀ {a} {A : Partial (Set a) i0} → PartialP i0 A
  {-# BUILTIN ISONEEMPTY isOneEmpty #-}

  primitive
    primPFrom1 : ∀ {a} {A : I → Set a} → A i1 → ∀ i j → Partial (A (primIMax i j)) i
    primPOr : ∀ {a} (i j : I) {A : Partial (Set a) (primIMax i j)}
              → PartialP i (λ z → A (IsOne1 i j z)) → PartialP j (λ z → A (IsOne2 i j z))
              → PartialP (primIMax i j) A
    primComp : ∀ {a} (A : (i : I) → Set (a i)) (φ : I) → (∀ i → Partial (A i) φ) → (a : A i0) → A i1

  syntax primPOr p q u t = [ p ↦ u , q ↦ t ]
