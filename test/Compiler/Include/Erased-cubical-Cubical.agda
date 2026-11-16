{-# OPTIONS --cubical --save-metas #-}

module Include.Erased-cubical-Cubical where

-- The code in this module should not be compiled. However, the
-- following re-exported code should be compiled.

open import Agda.Builtin.Bool public

postulate
  easy : {A : Set} → A

data Not-compiled : Set where
