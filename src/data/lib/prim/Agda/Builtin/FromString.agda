{-# OPTIONS --without-K --safe --no-sized-types --no-guardedness
            --no-subtyping #-}

module Agda.Builtin.FromString where

open import Agda.Primitive
open import Agda.Builtin.String

record IsString {a} (A : Set a) : Set (lsuc a) where
  field
    Constraint : String → Set a
    fromString : (s : String) {{_ : Constraint s}} → A

open IsString {{...}} public using (fromString)

{-# BUILTIN FROMSTRING fromString #-}
{-# DISPLAY IsString.fromString _ s = fromString s #-}
