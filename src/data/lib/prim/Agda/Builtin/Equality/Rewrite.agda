{-# OPTIONS --cubical-compatible --no-sized-types --no-guardedness --level-universe #-}

module Agda.Builtin.Equality.Rewrite where

open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

primitive primNoMatch : ∀ {a} {A : Set a} → A → A

⟨_⟩ : ∀ {a} {A : Set a} → A → A
⟨_⟩ = primNoMatch
