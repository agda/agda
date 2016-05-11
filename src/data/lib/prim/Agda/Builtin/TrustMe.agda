{-# OPTIONS --without-K #-}

module Agda.Builtin.TrustMe where

open import Agda.Builtin.Equality

primitive primTrustMe : ∀ {a} {A : Set a} {x y : A} → x ≡ y
