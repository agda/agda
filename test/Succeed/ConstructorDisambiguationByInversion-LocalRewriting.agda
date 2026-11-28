-- A local rewrite rule can change a result type after the inversion map
-- has been computed.  The map for `El` records `Original` and `Other`,
-- while `El true` reduces to `Rewritten` under the rule.  Selecting `Other.c`
-- from the map would discard the required `Rewritten.c`.

{-# OPTIONS --local-rewriting #-}

module ConstructorDisambiguationByInversion-LocalRewriting where

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

module _ (@rewrite eq : Original ≡ Rewritten) where
  _ : El true ≡ Rewritten
  _ = refl

  select : ∀ {i} → El i → i ≡ true → Rewritten
  select x refl = x

  test : Rewritten
  test = select c refl  -- At the index fixed by `refl`, only `Rewritten.c` fits.
