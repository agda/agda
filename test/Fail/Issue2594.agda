-- Andreas, 2017-10-08, issue #2594, reported by gallais

-- Incomplete pattern matching should be reported as such,
-- rather than crashing on a split error.

-- {-# OPTIONS -v tc.cover:10 #-}

open import Agda.Builtin.Bool

dispatch : Bool → Set
dispatch true  = Bool
dispatch false = Bool

argh : (b : Bool) → dispatch b → Bool
argh false false = true
argh false true  = false

-- Error was: Cannot split on non-datatype

-- Expected error:
-- Incomplete pattern matching
