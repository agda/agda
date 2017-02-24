------------------------------------------------------------------------
-- The Agda standard library
--
-- The Maybe type and some operations
------------------------------------------------------------------------

-- The definitions in this file are reexported by Data.Maybe.

module Data.Maybe.Base where

open import Level

data Maybe {a} (A : Set a) : Set a where
  just    : (x : A) → Maybe A
  nothing : Maybe A

{-# FOREIGN GHC type AgdaMaybe a b = Maybe b #-}
{-# COMPILE GHC Maybe = data MAlonzo.Code.Data.Maybe.Base.AgdaMaybe (Just | Nothing) #-}

------------------------------------------------------------------------
-- Some operations

open import Data.Bool.Base using (Bool; true; false; not)
open import Data.Unit.Base using (⊤)
open import Function
open import Relation.Nullary

boolToMaybe : Bool → Maybe ⊤
boolToMaybe true  = just _
boolToMaybe false = nothing

is-just : ∀ {a} {A : Set a} → Maybe A → Bool
is-just (just _) = true
is-just nothing  = false

is-nothing : ∀ {a} {A : Set a} → Maybe A → Bool
is-nothing = not ∘ is-just

decToMaybe : ∀ {a} {A : Set a} → Dec A → Maybe A
decToMaybe (yes x) = just x
decToMaybe (no _)  = nothing

-- A dependent eliminator.

maybe : ∀ {a b} {A : Set a} {B : Maybe A → Set b} →
        ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x
maybe j n (just x) = j x
maybe j n nothing  = n

-- A non-dependent eliminator.

maybe′ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → B → Maybe A → B
maybe′ = maybe

-- A safe variant of "fromJust". If the value is nothing, then the
-- return type is the unit type.

From-just : ∀ {a} (A : Set a) → Maybe A → Set a
From-just A (just _) = A
From-just A nothing  = Lift ⊤

from-just : ∀ {a} {A : Set a} (x : Maybe A) → From-just A x
from-just (just x) = x
from-just nothing  = _

-- Functoriality: map.

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
map f = maybe (just ∘ f) nothing

------------------------------------------------------------------------
-- Any and All

open Data.Bool.Base using (T)
open import Data.Empty using (⊥)

data Any {a p} {A : Set a} (P : A → Set p) : Maybe A → Set (a ⊔ p) where
  just : ∀ {x} (px : P x) → Any P (just x)

data All {a p} {A : Set a} (P : A → Set p) : Maybe A → Set (a ⊔ p) where
  just    : ∀ {x} (px : P x) → All P (just x)
  nothing : All P nothing

Is-just : ∀ {a} {A : Set a} → Maybe A → Set a
Is-just = Any (λ _ → ⊤)

Is-nothing : ∀ {a} {A : Set a} → Maybe A → Set a
Is-nothing = All (λ _ → ⊥)

to-witness : ∀ {p} {P : Set p} {m : Maybe P} → Is-just m → P
to-witness (just {x = p} _) = p

to-witness-T : ∀ {p} {P : Set p} (m : Maybe P) → T (is-just m) → P
to-witness-T (just p) _  = p
to-witness-T nothing  ()
