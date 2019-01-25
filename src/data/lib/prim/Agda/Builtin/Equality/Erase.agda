{-# OPTIONS --with-K --safe --no-sized-types --no-guardedness #-}

module Agda.Builtin.Equality.Erase where

open import Agda.Builtin.Equality

primitive primEraseEquality : ∀ {a} {A : Set a} {x y : A} → x ≡ y → x ≡ y
