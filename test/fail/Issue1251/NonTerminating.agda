module Issue1251.NonTerminating where

open import Common.Prelude  -- an import is necessary to trigger internal error

-- a non-termination function using imported stuff
bla : Nat → Set
bla zero    = bla zero
bla (suc x) = bla x
