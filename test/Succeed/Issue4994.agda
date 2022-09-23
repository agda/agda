{-# OPTIONS --rewriting --no-projection-like #-}
module _ where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Bool

data D (A : Set) : Set where
  con : (a : A) → D A

pr : ∀ {A} → D A → A
pr (con a) = a

postulate
  f : D Bool → Bool
  prf : pr ≡ f

{-# REWRITE prf #-}
