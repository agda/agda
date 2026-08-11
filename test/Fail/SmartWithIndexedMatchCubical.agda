{-# OPTIONS --smart-with --cubical-compatible #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

-- Unfortunately, '--smart-with' does not work nicely with '--cubical'
-- Indexed matches throw errors about the presence of interval variables

-- It might be worth considering whether we could somehow avoid generating
-- transport/hcomp clauses and just lose canonicity (like how indexed pattern
-- matching is already handled in places), but for now I think warnings
-- and errors are reasonable...

data IsTrue : Bool → Set where
  is-true : IsTrue true

foo : (b : Bool) → IsTrue b → b ≡ true
foo b p with is-true ← p = refl

bar : IsTrue true → Bool
bar p with is-true ← p = true
