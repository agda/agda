-- Andreas, 2016-10-09, re issue #2223

-- The front matter or module telescope of the top-level module
-- may generate level constraints that live in no module!

{-# OPTIONS -v tc.constr.add:45 #-} -- KEEP!

open import Common.Level
open import Issue2223.Setoids -- import necessary!

module _ (S : Setoid lzero lzero) (a : Setoid.Carrier S) (_ : a ⟨ Setoid._≈_ S ⟩ a) where

-- PROBLEM WAS: internal error in debug printing.
-- Should work now.
