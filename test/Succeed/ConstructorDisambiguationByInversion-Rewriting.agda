-- A rewrite rule can change a result type after the inversion map
-- for `El` has been computed.  The map contains `Original` and `Other`,
-- but the later rule makes `El true` reduce to `Rewritten`.  Treating the
-- map as exhaustive would select `Other.c` and discard `Rewritten.c`.
-- Disambiguation must wait for `refl` to fix the index to `true`.

{-# OPTIONS --rewriting --confluence-check #-}

module ConstructorDisambiguationByInversion-Rewriting where

open import Agda.Builtin.Bool using (Bool ; false ; true)
open import Agda.Builtin.Equality using (_≡_ ; refl)
import Agda.Builtin.Equality.Rewrite

postulate Original : Set

data Other : Set where
  c : Other

data Rewritten : Set where
  c : Rewritten

El : Bool → Set
El true  = Original
El false = Other

postulate change : Original ≡ Rewritten
{-# REWRITE change #-}

_ : El true ≡ Rewritten
_ = refl

select : ∀ {i} → El i → i ≡ true → Rewritten
select x refl = x

test : Rewritten
test = select c refl  -- The equality fixes the index to `true`, so `c` is `Rewritten.c`.
