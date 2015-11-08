
module _ where

open import Common.Prelude
open import Common.String

record IsString {a} (A : Set a) : Set a where
  field
    fromString : String → A

open IsString {{...}} public
{-# BUILTIN FROMSTRING fromString #-}

instance
  StringIsString : IsString String
  StringIsString = record { fromString = λ s → s }

  ListIsString : IsString (List Char)
  ListIsString = record { fromString = stringToList }

foo : List Char
foo = "foo"

open import Common.Equality

thm : "foo" ≡ 'f' ∷ 'o' ∷ 'o' ∷ []
thm = refl
