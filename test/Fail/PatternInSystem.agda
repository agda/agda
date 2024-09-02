-- Andreas, 2024-08-01
-- Trigger error PatternInSystem

{-# OPTIONS --cubical #-}

open import Agda.Primitive            using ()
  renaming (Set to Type)
open import Agda.Primitive.Cubical    using (I; i0; i1)
  renaming (primHComp to hcomp ; primTransp to transp)
open import Agda.Builtin.Cubical.Path using (PathP; _≡_)

data S¹ : Type where
  base : S¹
  loop : base ≡ base

trigger : PathP _ _ _
trigger j =
  transp (λ _ → S¹ → S¹) i0
    (hcomp (λ { i (j = i0) base → base
              ; i (j = i1) base → base
              })
           _)

-- Expected error:
--
-- Pattern matching or path copatterns not allowed in systems
