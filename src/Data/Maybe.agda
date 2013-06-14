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

open import Data.Bool using (Bool; true; false; not)
open import Data.Unit using (⊤)
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

------------------------------------------------------------------------
-- Maybe monad

open import Category.Functor
open import Category.Monad
open import Category.Monad.Identity

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → Maybe A → Maybe B
map f = maybe (just ∘ f) nothing

functor : ∀ {f} → RawFunctor (Maybe {a = f})
functor = record
  { _<$>_ = map
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

open Data.Bool using (T)
open import Data.Empty using (⊥)
import Relation.Nullary.Decidable as Dec
open import Relation.Unary as U

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

anyDec : ∀ {a p} {A : Set a} {P : A → Set p} →
         U.Decidable P → U.Decidable (Any P)
anyDec p nothing  = no λ()
anyDec p (just x) = Dec.map′ just (λ { (Any.just px) → px }) (p x)

allDec : ∀ {a p} {A : Set a} {P : A → Set p} →
         U.Decidable P → U.Decidable (All P)
allDec p nothing  = yes nothing
allDec p (just x) = Dec.map′ just (λ { (All.just px) → px }) (p x)
