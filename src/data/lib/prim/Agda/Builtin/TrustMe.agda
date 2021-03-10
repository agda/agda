{-# OPTIONS --no-sized-types --no-guardedness --no-subtyping #-}

module Agda.Builtin.TrustMe where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Erase

private
  postulate
    unsafePrimTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y

primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
primTrustMe = primEraseEquality unsafePrimTrustMe

{-# DISPLAY primEraseEquality unsafePrimTrustMe = primTrustMe #-}
