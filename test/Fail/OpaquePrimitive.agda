{-# OPTIONS -Werror #-}
module OpaquePrimitive where

open import Agda.Builtin.Equality

postulate Char : Set

{-# BUILTIN CHAR Char #-}

opaque primitive
  primToUpper : Char → Char

_ : primToUpper 'a' ≡ 'A'
_ = refl
