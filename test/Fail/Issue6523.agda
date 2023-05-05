{-# OPTIONS --guarded #-}
module Issue6523 where

open import Agda.Primitive

module Prims where
  primitive
    primLockUniv : Set₁

open Prims renaming (primLockUniv to LockU) public

private
  variable
    l : Level
    A B : Set l

-- We postulate Tick as it is supposed to be an abstract sort.
postulate
  Tick : LockU

▹_ : ∀ {l} → Set l → Set l
▹_ A = (@tick x : Tick) → A

▸_ : ∀ {l} → ▹ Set l → Set l
▸ A = (@tick x : Tick) → A x

next : A → ▹ A
next x _ = x

_⊛_ : ▹ (A → B) → ▹ A → ▹ B
_⊛_ f x a = f a (x a)

----------------------------------
-- The bug

-- definition of untic is illegal: since tic is not marked @tic we have
-- no idea where to split the context to check the function
untic : ∀ {ℓ} {X : Set ℓ} → Tick → ▹ X → X
untic tic later = later tic

-- This shouldn't be possible for Later
-- The call to untic should be forbidden
join : ∀ {A : Set} → ▹ (▹ A) → ▹ A
join x tic = untic tic (x tic)
