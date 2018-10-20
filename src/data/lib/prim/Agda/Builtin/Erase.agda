{-# OPTIONS --without-K #-}

module Agda.Builtin.Erase where

open import Agda.Builtin.Equality

primitive primErase : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
