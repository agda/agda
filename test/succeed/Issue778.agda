-- {-# OPTIONS -v tc.term.exlam:100 -v extendedlambda:100 -v int2abs.reifyterm:100 #-}
-- Andreas, 2013-02-26
module Issue778 (Param : Set) where

open import Common.Prelude

works : Nat → Nat
works with zero
... | zero = λ { zero → zero; (suc x) → suc x }
... | suc _ = λ { x → x }

test : Nat → Nat
test = λ { zero → zero; (suc x) → aux x }
  where aux : Nat → Nat
        aux x with works x
        ... | zero  = zero
        ... | suc y = works y
-- There was a internal error in connection to extended lambda and
-- where blocks in parametrized modules.
