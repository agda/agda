{-# OPTIONS --no-keep-pattern-variables #-}

module Issue3080 where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

data Fin (m : Nat) : Set where
  fzero' : (n : Nat) (p : m ≡ suc n) → Fin m
  fsuc'  : (n : Nat) (p : m ≡ suc n) (i : Fin n) → Fin m

lift : (m : Nat) (i : Fin m) → Fin (suc m)
lift m (fzero' n p)  = {!p!}
lift m (fsuc' n p i) = {!p!} -- Split on p here

module PatternSynonyms where

  pattern fzero n      = fzero' n refl
  pattern fsuc  n i    = fsuc'  n refl i

-- Splitting produces
--
--   lift .(suc n) (.Issue3080.PatternSynonyms.fsuc n i) = ?
--
-- which fails to parse.
