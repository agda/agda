-- Andreas, 2026-08-29, issue #8697
-- Auxiliary module: exports both zeros through its interface.

{-# OPTIONS --safe #-}

module Issue8697.Zeros where

open import Agda.Builtin.Float

-- A fixity level is also a Double in the interface,
-- and fixities are serialized before the definitions.
infix 0 _!
_! : Float → Float
x ! = x

+zero : Float
+zero = 0.0

-zero : Float
-zero = -0.0

nan : Float
nan = primFloatDiv 0.0 0.0

inf : Float
inf = primFloatDiv 1.0 0.0

-inf : Float
-inf = primFloatDiv -1.0 0.0
