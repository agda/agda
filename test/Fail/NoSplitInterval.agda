{-# OPTIONS --cubical --omega-in-omega #-}

open import Agda.Primitive.Cubical
open import Agda.Builtin.Bool

-- With --omega-in-omega we are allowed to split on Setω datatypes.
-- Andrea 22/05/2020: in the future we might be allowed even without --omega-in-omega.

-- This test makes sure the interval I is still special cased and splitting is forbidden.

bad : I → Bool
bad i0 = true
bad i1 = false
