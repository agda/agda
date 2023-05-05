{-# OPTIONS --erasure #-}

-- Andreas, 2018-10-17
--
-- Cannot branch on erased argument.

open import Agda.Builtin.Bool

T : @0 Bool → Set
T true  = Bool
T false = Bool → Bool

-- Should fail with error like:
--
-- Cannot branch on erased argument of datatype Bool
-- when checking the definition of T
