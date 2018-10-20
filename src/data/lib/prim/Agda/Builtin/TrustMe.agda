{-# OPTIONS --without-K #-}

module Agda.Builtin.TrustMe where

open import Agda.Builtin.Equality
open import Agda.Builtin.Erase

primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
primTrustMe {x = x} {y} = primErase unsafePrimTrustMe
  where postulate unsafePrimTrustMe : x ≡ y
