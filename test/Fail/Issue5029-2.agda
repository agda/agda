{-# OPTIONS --safe -WnoSafeFlagNoCoverageCheck #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality

data ⊥ : Set where

{-# NON_COVERING #-}

f : ∀ b → b ≡ true → ⊥
f false ()

bad : ⊥
bad = f true refl
