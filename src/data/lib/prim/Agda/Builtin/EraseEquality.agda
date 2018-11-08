{-# OPTIONS --with-K #-}

module Agda.Builtin.EraseEquality where

open import Agda.Builtin.Equality

primitive primEraseEquality : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
