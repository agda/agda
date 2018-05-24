
module _ where

module M (X : Set₁) where

  record Raw : Set₁ where
    field return : Set
    postulate fmap : Set

  module Fails = Raw ⦃ … ⦄
  module Works ⦃ r : Raw ⦄ = Raw r

open M

postulate r : Raw Set

fail : Set
fail = Fails.fmap Set ⦃ r ⦄
-- C-c C-n fail
-- M.Raw.fmap Set r

good : Set
good = Works.fmap Set ⦃ r ⦄
-- C-c C-n good
-- M.Raw.fmap r

-- Checking using reflection saves us an interaction test.

open import Agda.Builtin.Reflection renaming (bindTC to _>>=_)
open import Agda.Builtin.Equality
open import Agda.Builtin.List
open import Agda.Builtin.Unit

macro
  `_ : Name → Term → TC ⊤
  (` x) hole = do
    v  ← normalise (def x [])
    `v ← quoteTC v
    unify hole `v

pattern vArg x = arg (arg-info visible relevant) x
pattern hArg x = arg (arg-info hidden  relevant) x
pattern `fmap x y = def (quote M.Raw.fmap) (x ∷ y ∷ [])
`Set = agda-sort (lit 0)
`r   = def (quote r) []

check-good : ` good ≡ `fmap (hArg `Set) (vArg `r)
check-good = refl

check-bad : ` fail ≡ ` good
check-bad = refl
