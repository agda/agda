{-# OPTIONS --erased-cubical --save-metas #-}

module Erased-cubical-Pattern-matching-Erased where

open import Agda.Builtin.String
open import Erased-cubical-Pattern-matching-Cubical

-- If c₁ and c₂ are treated as erased, then f might be compiled to
-- something akin to ⊥-elim. However, the main module uses
-- --cubical, not --erased-cubical, so f should not be compiled in
-- that way.

f : D → String
f c₁ = "Success\n"
f c₂ = "Failure\n"
