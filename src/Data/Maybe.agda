------------------------------------------------------------------------
-- The Agda standard library
--
-- The Maybe type
------------------------------------------------------------------------

module Data.Maybe where

open import Level
open import Function
open import Relation.Nullary

------------------------------------------------------------------------
-- The type and some operations

open import Data.Maybe.Minimal public

------------------------------------------------------------------------
-- Maybe monad

open import Category.Functor
open import Category.Monad
open import Category.Monad.Identity

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
-- Any and All are preserving decidability

import Relation.Nullary.Decidable as Dec
open import Relation.Unary as U

anyDec : ∀ {a p} {A : Set a} {P : A → Set p} →
         U.Decidable P → U.Decidable (Any P)
anyDec p nothing  = no λ()
anyDec p (just x) = Dec.map′ just (λ { (Any.just px) → px }) (p x)

allDec : ∀ {a p} {A : Set a} {P : A → Set p} →
         U.Decidable P → U.Decidable (All P)
allDec p nothing  = yes nothing
allDec p (just x) = Dec.map′ just (λ { (All.just px) → px }) (p x)
