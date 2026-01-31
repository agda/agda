{-# OPTIONS --no-sized-types --no-guardedness --level-universe
            --erasure #-}

module Agda.Builtin.TrustMe where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Erase

private
  postulate
    unsafePrimTrustMe : ∀ {@0 a} {A : Set a} {x y : A} → x ≡ y

primTrustMe : ∀ {@0 a} {A : Set a} {x y : A} → x ≡ y
primTrustMe = primEraseEquality unsafePrimTrustMe

{-# DISPLAY primEraseEquality unsafePrimTrustMe = primTrustMe #-}
