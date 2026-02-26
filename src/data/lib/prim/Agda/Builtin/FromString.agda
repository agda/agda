{-# OPTIONS --cubical-compatible --safe --no-sized-types
            --no-guardedness --level-universe --erasure #-}

module Agda.Builtin.FromString where

open import Agda.Primitive
open import Agda.Builtin.String

record IsString {@0 a} (A : Set a) : Set (lsuc a) where
  field
    Constraint : String → Set a
    fromString : (s : String) {{_ : Constraint s}} → A

open IsString {{...}} public using (fromString)

{-# BUILTIN FROMSTRING fromString #-}
{-# DISPLAY IsString.fromString _ s = fromString s #-}
