-- Andreas, 2026-02-04, issue #8365
-- 'reduce' in wrong context caused a crash in the presence of rewriting.
-- Report and original test by Constantine Theocharis, shrunk by Szumi Xie.

{-# OPTIONS --rewriting #-}

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

postulate
  eq : Bool → Bool → Bool
  eq-id : (x : Bool) → eq x x ≡ true
  {-# REWRITE eq-id #-}

g : (f : Bool → Bool) → eq (f false) (f true) ≡ true → Bool
g f refl = true

-- WAS: internal error due to out-of scope de Bruijn index

-- Expected error: [SplitError.UnificationStuck]
-- I'm not sure if there should be a case for the constructor refl,
-- because I get stuck when trying to solve the following unification
-- problems (inferred index ≟ expected index):
--   eq (f false) (f true) ≟ true
-- when checking that the pattern refl has type
-- eq (f false) (f true) ≡ true
