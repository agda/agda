------------------------------------------------------------------------
-- The Agda standard library
--
-- The Maybe type
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Maybe monad

open import Function
open import Category.Functor
open import Category.Monad
open import Category.Monad.Identity

functor : ∀ {f} → RawFunctor (Maybe {a = f})
functor = record
  { _<$>_ = λ f → maybe (just ∘ f) nothing
  }

monadT : ∀ {f} {M : Set f → Set f} →
         RawMonad M → RawMonad (λ A → M (Maybe A))
monadT M = record
  { return = M.return ∘ just
  ; _>>=_  = λ m f → M._>>=_ m (maybe f (M.return nothing))
  }
  where module M = RawMonad M

monad : ∀ {f} → RawMonad (Maybe {a = f})
monad = monadT IdentityMonad

monadZero : ∀ {f} → RawMonadZero (Maybe {a = f})
monadZero = record
  { monad = monad
  ; ∅     = nothing
  }

monadPlus : ∀ {f} → RawMonadPlus (Maybe {a = f})
monadPlus {f} = record
  { monadZero = monadZero
  ; _∣_       = _∣_
  }
  where
  _∣_ : {A : Set f} → Maybe A → Maybe A → Maybe A
  nothing ∣ y = y
  just x  ∣ y = just x

------------------------------------------------------------------------
-- Equality

open import Relation.Nullary
open import Relation.Binary as B

data Eq {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) : Rel (Maybe A) (a ⊔ ℓ) where
  just    : ∀ {x y} (x≈y : x ≈ y) → Eq _≈_ (just x) (just y)
  nothing : Eq _≈_ nothing nothing

drop-just : ∀ {a ℓ} {A : Set a} {_≈_ : Rel A ℓ} {x y : A} →
            just x ⟨ Eq _≈_ ⟩ just y → x ≈ y
drop-just (just x≈y) = x≈y

setoid : ∀ {ℓ₁ ℓ₂} → Setoid ℓ₁ ℓ₂ → Setoid _ _
setoid S = record
  { Carrier       = Maybe S.Carrier
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  module S = Setoid S
  _≈_ = Eq S._≈_

  refl : ∀ {x} → x ≈ x
  refl {just x}  = just S.refl
  refl {nothing} = nothing

  sym : ∀ {x y} → x ≈ y → y ≈ x
  sym (just x≈y) = just (S.sym x≈y)
  sym nothing    = nothing

  trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  trans (just x≈y) (just y≈z) = just (S.trans x≈y y≈z)
  trans nothing    nothing    = nothing

decSetoid : ∀ {ℓ₁ ℓ₂} → DecSetoid ℓ₁ ℓ₂ → DecSetoid _ _
decSetoid D = record
  { isDecEquivalence = record
    { isEquivalence = Setoid.isEquivalence (setoid (DecSetoid.setoid D))
    ; _≟_           = _≟_
    }
  }
  where
  _≟_ : B.Decidable (Eq (DecSetoid._≈_ D))
  just x  ≟ just y  with DecSetoid._≟_ D x y
  just x  ≟ just y  | yes x≈y = yes (just x≈y)
  just x  ≟ just y  | no  x≉y = no (x≉y ∘ drop-just)
  just x  ≟ nothing = no λ()
  nothing ≟ just y  = no λ()
  nothing ≟ nothing = yes nothing

------------------------------------------------------------------------
-- Any and All

open import Data.Empty using (⊥)
import Relation.Nullary.Decidable as Dec
open import Relation.Unary as U

data Any {a} {A : Set a} (P : A → Set a) : Maybe A → Set a where
  just : ∀ {x} (px : P x) → Any P (just x)

data All {a} {A : Set a} (P : A → Set a) : Maybe A → Set a where
  just    : ∀ {x} (px : P x) → All P (just x)
  nothing : All P nothing

IsJust : ∀ {a} {A : Set a} → Maybe A → Set a
IsJust = Any (λ _ → Lift ⊤)

IsNothing : ∀ {a} {A : Set a} → Maybe A → Set a
IsNothing = All (λ _ → Lift ⊥)

private

  drop-just-Any : ∀ {A} {P : A → Set} {x} → Any P (just x) → P x
  drop-just-Any (just px) = px

  drop-just-All : ∀ {A} {P : A → Set} {x} → All P (just x) → P x
  drop-just-All (just px) = px

anyDec : ∀ {A} {P : A → Set} → U.Decidable P → U.Decidable (Any P)
anyDec p nothing  = no λ()
anyDec p (just x) = Dec.map′ just drop-just-Any (p x)

allDec : ∀ {A} {P : A → Set} → U.Decidable P → U.Decidable (All P)
allDec p nothing  = yes nothing
allDec p (just x) = Dec.map′ just drop-just-All (p x)
