{-# OPTIONS --erased-cubical --no-main --save-metas #-}

open import Agda.Builtin.Bool

open import Erased-cubical-Cubical

postulate
  f : Not-compiled → Bool

-- It is at the time of writing not possible to give a COMPILE GHC
-- pragma for f, because Not-compiled is not compiled.

{-# COMPILE GHC f = \_ -> True #-}
