------------------------------------------------------------------------
-- The Maybe type
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Data.Maybe where

open import Level

------------------------------------------------------------------------
-- The type

open import Data.Maybe.Core public

------------------------------------------------------------------------
-- Some operations

open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤)

boolToMaybe : Bool → Maybe ⊤
boolToMaybe true  = just _
boolToMaybe false = nothing

maybeToBool : ∀ {a} {A : Set a} → Maybe A → Bool
maybeToBool (just _) = true
maybeToBool nothing  = false

-- A non-dependent eliminator.

maybe : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → B → Maybe A → B
maybe j n (just x) = j x
maybe j n nothing  = n

------------------------------------------------------------------------
-- Maybe monad

open import Function
open import Category.Functor
open import Category.Monad
open import Category.Monad.Identity

functor : RawFunctor Maybe
functor = record
  { _<$>_ = λ f → maybe (just ∘ f) nothing
  }

monadT : ∀ {M} → RawMonad M → RawMonad (λ A → M (Maybe A))
monadT M = record
  { return = M.return ∘ just
  ; _>>=_  = λ m f → M._>>=_ m (maybe f (M.return nothing))
  }
  where module M = RawMonad M

monad : RawMonad Maybe
monad = monadT IdentityMonad

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
  _∣_ : ∀ {a : Set} → Maybe a → Maybe a → Maybe a
  nothing ∣ y = y
  just x  ∣ y = just x

------------------------------------------------------------------------
-- Equality

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

drop-just : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
drop-just refl = refl

decSetoid : {A : Set} → Decidable (_≡_ {A = A}) → DecSetoid _ _
decSetoid {A} _A-≟_ = PropEq.decSetoid _≟_
  where
  _≟_ : Decidable (_≡_ {A = Maybe A})
  just x  ≟ just y  with x A-≟ y
  just x  ≟ just .x | yes refl = yes refl
  just x  ≟ just y  | no  x≢y    = no (x≢y ∘ drop-just)
  just x  ≟ nothing = no λ()
  nothing ≟ just y  = no λ()
  nothing ≟ nothing = yes refl

------------------------------------------------------------------------
-- Any and All

open import Data.Product using (_,_)
open import Data.Empty using (⊥)
import Relation.Nullary.Decidable as Dec

data Any {a} {A : Set a} (P : A → Set a) : Maybe A → Set a where
  just : ∀ {x} (px : P x) → Any P (just x)

data All {a} {A : Set a} (P : A → Set a) : Maybe A → Set a where
  just    : ∀ {x} (px : P x) → All P (just x)
  nothing : All P nothing

IsJust : ∀ {A : Set} → Maybe A → Set
IsJust = Any (λ _ → ⊤)

IsNothing : ∀ {A} → Maybe A → Set
IsNothing = All (λ _ → ⊥)

private

  drop-just-Any : ∀ {A} {P : A → Set} {x} → Any P (just x) → P x
  drop-just-Any (just px) = px

  drop-just-All : ∀ {A} {P : A → Set} {x} → All P (just x) → P x
  drop-just-All (just px) = px

anyDec : ∀ {A} {P : A → Set} →
         (∀ x → Dec (P x)) → (x : Maybe A) → Dec (Any P x)
anyDec p nothing  = no λ()
anyDec p (just x) = Dec.map (just , drop-just-Any) (p x)

allDec : ∀ {A} {P : A → Set} →
         (∀ x → Dec (P x)) → (x : Maybe A) → Dec (All P x)
allDec p nothing  = yes nothing
allDec p (just x) = Dec.map (just , drop-just-All) (p x)
