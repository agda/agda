{-# OPTIONS --erased-cubical --erasure #-}

open import Erased-cubical-Pattern-matching.Cubical

-- The following definition should be rejected. Matching on a
-- non-erased constructor that is treated as erased because it was
-- defined in a module that uses --cubical should not on its own make
-- it possible to use erased definitions in the right-hand side.

f : D → D
f c = c
