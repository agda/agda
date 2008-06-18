------------------------------------------------------------------------
-- The Maybe type
------------------------------------------------------------------------

module Data.Maybe where

------------------------------------------------------------------------
-- The type

data Maybe (A : Set) : Set where
  just    : (x : A) -> Maybe A
  nothing : Maybe A

------------------------------------------------------------------------
-- Some operations

open import Data.Bool
open import Data.Unit

boolToMaybe : Bool -> Maybe ⊤
boolToMaybe true  = just _
boolToMaybe false = nothing

maybeToBool : Maybe ⊤ -> Bool
maybeToBool (just _) = true
maybeToBool nothing  = false

-- A non-dependent eliminator.

maybe : {a b : Set} -> (a -> b) -> b -> Maybe a -> b
maybe j n (just x) = j x
maybe j n nothing  = n

maybe₀₁ : {a : Set} {b : Set1} -> (a -> b) -> b -> Maybe a -> b
maybe₀₁ j n (just x) = j x
maybe₀₁ j n nothing  = n

------------------------------------------------------------------------
-- Maybe monad

open import Category.Monad

MaybeMonad : RawMonad Maybe
MaybeMonad = record
  { return = just
  ; _>>=_  = _>>=_
  }
  where
  _>>=_ : forall {a b} -> Maybe a -> (a -> Maybe b) -> Maybe b
  nothing >>= f = nothing
  just x  >>= f = f x

MaybeMonadZero : RawMonadZero Maybe
MaybeMonadZero = record
  { monad = MaybeMonad
  ; ∅     = nothing
  }

MaybeMonadPlus : RawMonadPlus Maybe
MaybeMonadPlus = record
  { monadZero = MaybeMonadZero
  ; _∣_       = _∣_
  }
  where
  _∣_ : forall {a} -> Maybe a -> Maybe a -> Maybe a
  nothing ∣ y = y
  just x  ∣ y = just x
