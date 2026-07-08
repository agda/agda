{-# OPTIONS --smart-with #-}

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

data ⊥ : Set where

data Branch : Set where
  branch : (Nat → Nat → Branch) → Branch

rec : Branch → ⊥
rec (branch f) = rec (f 0 0)

-- After turning 'p' or 'q' into a rewrite rule, 'f'/'g' become underapplied
foo : (f : Nat → Nat → Branch) (g : Nat → Branch) → f 0 ≡ g → g 0 ≡ branch f
    → Nat
foo f g p q rewrite p rewrite q = {!!}
