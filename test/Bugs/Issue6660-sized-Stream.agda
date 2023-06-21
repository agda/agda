-- Andreas, 2023-06-21, issue #6660
-- Constructor inlining does not work for sized types,
-- because the type checker has limitations.

{-# OPTIONS --sized-types #-}

open import Agda.Builtin.Size

record Stream (i : Size) (A : Set) : Set where
  coinductive; constructor _∷_
  field
    head  : A
    tail  : ∀ {j : Size< i} → Stream j A
open Stream public

{-# INLINE _∷_ #-}

zipWith : {i : Size} {A B C : Set} (f : A → B → C) → Stream i A → Stream i B → Stream i C
zipWith f s t = f (s .head) (t .head) ∷ zipWith f (s .tail) (t .tail)

-- Should succeed

-- Current error:
-- Stream _i_15 _C_18 !=< ({j : Size< i} → Stream j C)
-- when checking that the inferred type of an application
--   Stream _i_15 _C_18
-- matches the expected type
--   {j : Size< i} → Stream j C
