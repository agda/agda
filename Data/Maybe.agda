------------------------------------------------------------------------
-- The Maybe type
------------------------------------------------------------------------

module Data.Maybe where

------------------------------------------------------------------------
-- The type

data Maybe (A : Set) : Set where
  just    : (x : A) → Maybe A
  nothing : Maybe A

------------------------------------------------------------------------
-- Some operations

open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤)

boolToMaybe : Bool → Maybe ⊤
boolToMaybe true  = just _
boolToMaybe false = nothing

maybeToBool : ∀ {A} → Maybe A → Bool
maybeToBool (just _) = true
maybeToBool nothing  = false

-- A non-dependent eliminator.

maybe : {a b : Set} → (a → b) → b → Maybe a → b
maybe j n (just x) = j x
maybe j n nothing  = n

maybe₀₁ : {a : Set} {b : Set1} → (a → b) → b → Maybe a → b
maybe₀₁ j n (just x) = j x
maybe₀₁ j n nothing  = n

------------------------------------------------------------------------
-- Maybe monad

open import Data.Function
open import Category.Functor
open import Category.Monad

functor : RawFunctor Maybe
functor = record
  { _<$>_ = λ f → maybe (just ∘ f) nothing
  }

monad : RawMonad Maybe
monad = record
  { return = just
  ; _>>=_  = _>>=_
  }
  where
  _>>=_ : ∀ {a b} → Maybe a → (a → Maybe b) → Maybe b
  nothing >>= f = nothing
  just x  >>= f = f x

monadZero : RawMonadZero Maybe
monadZero = record
  { monad = monad
  ; ∅     = nothing
  }

monadPlus : RawMonadPlus Maybe
monadPlus = record
  { monadZero = monadZero
  ; _∣_       = _∣_
  }
  where
  _∣_ : ∀ {a} → Maybe a → Maybe a → Maybe a
  nothing ∣ y = y
  just x  ∣ y = just x

------------------------------------------------------------------------
-- Equality

open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_; refl)

drop-just : ∀ {A} {x y : A} → just x ≡ just y → x ≡ y
drop-just refl = refl

decSetoid : ∀ {A} → Decidable (_≡_ {A}) → DecSetoid
decSetoid {A} _A-≟_ = PropEq.decSetoid _≟_
  where
  _≟_ : Decidable (_≡_ {Maybe A})
  just x  ≟ just y  with x A-≟ y
  just x  ≟ just .x | yes refl = yes refl
  just x  ≟ just y  | no  x≢y    = no (x≢y ∘ drop-just)
  just x  ≟ nothing = no λ()
  nothing ≟ just y  = no λ()
  nothing ≟ nothing = yes refl
