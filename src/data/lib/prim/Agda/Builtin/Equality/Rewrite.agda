{-# OPTIONS --cubical-compatible --no-sized-types --no-guardedness --level-universe #-}

module Agda.Builtin.Equality.Rewrite where

open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

primitive primNoMatch : ∀ {@0 a} {A : Set a} → A → A

⟨_⟩ : ∀ {@0 a} {A : Set a} → A → A
⟨_⟩ = primNoMatch
