
-- Andreas, 2020-11-18, issue #5065, reported by nad
-- Termination checker regresssion in Agda 2.6.1

-- {-# OPTIONS -v term.reduce:80 #-}

open import Agda.Builtin.Bool

bad : Bool → Bool
bad b with bad b
… | true  = bad b
… | false = true

-- Termination checker loops in Agda 2.6.1.

-- Expected error (works in <= 2.6.0 and now again in 2.6.2):
--
-- Termination checking failed for the following functions:
--   bad
-- Problematic calls:
--   bad b
