module WarningOnUsage where

id : {A : Set} → A → A
id x = x



-- Deprecated names

λx→x = id

{-# WARNING_ON_USAGE λx→x "DEPRECATED: Use `id` instead of `λx→x`" #-}

open import Agda.Builtin.Equality

_ : {A : Set} {x : A} → λx→x x ≡ x
_ = refl
