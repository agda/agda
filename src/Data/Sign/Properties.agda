------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties about signs
------------------------------------------------------------------------

module Data.Sign.Properties where

open import Data.Empty
open import Function
open import Data.Sign
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties (_≡_ {A = Sign})

-- The opposite of a sign is not equal to the sign.

opposite-not-equal : ∀ s → s ≢ opposite s
opposite-not-equal - ()
opposite-not-equal + ()

opposite-cong : ∀ {s t} → opposite s ≡ opposite t → s ≡ t
opposite-cong { - } { - } refl = refl
opposite-cong { - } { + } ()
opposite-cong { + } { - } ()
opposite-cong { + } { + } refl = refl

------------------------------------------------------------------------
-- _*_

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

cancel-*-right : RightCancellative _*_
cancel-*-right - - _  = refl
cancel-*-right - + eq = ⊥-elim (opposite-not-equal _ $ sym eq)
cancel-*-right + - eq = ⊥-elim (opposite-not-equal _ eq)
cancel-*-right + + _  = refl

cancel-*-left : LeftCancellative _*_
cancel-*-left - eq = opposite-cong eq
cancel-*-left + eq = eq

*-cancellative : Cancellative _*_
*-cancellative = cancel-*-left , cancel-*-right

s*s≡+ : ∀ s → s * s ≡ +
s*s≡+ + = refl
s*s≡+ - = refl
