module ProjPDisplay where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma

record is-contr (A : Set) : Set where
  field
    centre : A
    paths : ∀ x → centre ≡ x

open is-contr public

private variable
  A B : Set

fibre : (A → B) → B → Set _
fibre {A = A} f y = Σ A λ x → f x ≡ y

record is-equiv (f : A → B) : Set where
  no-eta-equality
  field
    is-eqv : (y : B) → is-contr (fibre f y)

_≃_ : Set → Set → Set _
_≃_ A B = Σ (A → B) is-equiv

open is-equiv

equiv→inverse : {f : A → B} → is-equiv f → B → A
equiv→inverse eqv y = eqv .is-eqv y .centre .fst

module Equiv {A B : Set} (f : A ≃ B) where
  to = f .fst
  from = equiv→inverse (f .snd)

-- This display form needs us to accurately remember whether a name on
-- the LHS is a projection or a definition.
{-# DISPLAY snd f .is-eqv y .centre .fst = Equiv.from f y #-}

module _ {A B : Set} (f : A ≃ B) (g : B → A) where
  -- Should be: g x != Equiv.from f x

  _ : g ≡ Equiv.from f
  _ = refl
