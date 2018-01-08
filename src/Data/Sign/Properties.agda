------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about signs
------------------------------------------------------------------------

module Data.Sign.Properties where

open import Algebra
open import Algebra.Structures
open import Data.Empty
open import Function
open import Data.Sign
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties (_≡_ {A = Sign})

-- The opposite of a sign is not equal to the sign.

s≢opposite[s] : ∀ s → s ≢ opposite s
s≢opposite[s] - ()
s≢opposite[s] + ()

opposite-injective : ∀ {s t} → opposite s ≡ opposite t → s ≡ t
opposite-injective { - } { - } refl = refl
opposite-injective { - } { + } ()
opposite-injective { + } { - } ()
opposite-injective { + } { + } refl = refl

------------------------------------------------------------------------
-- _*_

-- Algebraic properties of _*_

*-identityˡ : LeftIdentity + _*_
*-identityˡ _ = refl

*-identityʳ : RightIdentity + _*_
*-identityʳ - = refl
*-identityʳ + = refl

*-identity : Identity + _*_
*-identity = *-identityˡ  , *-identityʳ

*-comm : Commutative _*_
*-comm + + = refl
*-comm + - = refl
*-comm - + = refl
*-comm - - = refl

*-assoc : Associative _*_
*-assoc + + _ = refl
*-assoc + - _ = refl
*-assoc - + _ = refl
*-assoc - - + = refl
*-assoc - - - = refl

*-cancelʳ-≡ : RightCancellative _*_
*-cancelʳ-≡ - - _  = refl
*-cancelʳ-≡ - + eq = ⊥-elim (s≢opposite[s] _ $ sym eq)
*-cancelʳ-≡ + - eq = ⊥-elim (s≢opposite[s] _ eq)
*-cancelʳ-≡ + + _  = refl

*-cancelˡ-≡ : LeftCancellative _*_
*-cancelˡ-≡ - eq = opposite-injective eq
*-cancelˡ-≡ + eq = eq

*-cancel-≡ : Cancellative _*_
*-cancel-≡ = *-cancelˡ-≡ , *-cancelʳ-≡

*-isSemigroup : IsSemigroup _≡_ _*_
*-isSemigroup = record
  { isEquivalence = isEquivalence
  ; assoc         = *-assoc
  ; ∙-cong        = cong₂ _*_
  }

*-semigroup : Semigroup _ _
*-semigroup = record
  { Carrier     = Sign
  ; _≈_         = _≡_
  ; _∙_         = _*_
  ; isSemigroup = *-isSemigroup
  }

*-isMonoid : IsMonoid _≡_ _*_ +
*-isMonoid = record
    { isSemigroup = *-isSemigroup
    ; identity    = *-identity
    }

*-monoid : Monoid _ _
*-monoid = record
  { Carrier  = Sign
  ; _≈_      = _≡_
  ; _∙_      = _*_
  ; ε        = +
  ; isMonoid = *-isMonoid
  }

-- Other properties of _*_

s*s≡+ : ∀ s → s * s ≡ +
s*s≡+ + = refl
s*s≡+ - = refl

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

opposite-not-equal = s≢opposite[s]
opposite-cong      = opposite-injective
cancel-*-left      = *-cancelˡ-≡
cancel-*-right     = *-cancelʳ-≡
*-cancellative     = *-cancel-≡
