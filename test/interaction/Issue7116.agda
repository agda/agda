module _ (A : Set) where

open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma

data Color : Set where
  black : Color

data Tree' : Color → Nat → Set where
  nb : ∀ (a : A) {c} {n}
     → Tree' c n
     → Tree' black n
     → Tree' black (suc n)

test : ∀ (a : A) {n} (l : Tree' black (suc n)) → Σ _ λ c → Tree' c (suc n)
test a (nb b l r) = {!!}   -- C-c C-a
-- was: internal error
-- should be: black , nb a r r

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: __IMPOSSIBLE__, called at src/full/Agda/TypeChecking/CompiledClause/Match.hs:87:73
