{-# OPTIONS --guarded --cubical=compatible #-}
module Agda.Primitive.Guarded where

open import Agda.Builtin.Equality

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

postulate
  löb : ∀ {l} {A : Set l} → (((@tick x : Tick) → A) → A) → A
  löbβ : ∀ {l} {A : Set l} → (f : ((@tick x : Tick) → A) → A) → löb f ≡ f (λ _ → (löb f))
    -- So in Cubical Agda, we will have to extract a path from löbβ.
