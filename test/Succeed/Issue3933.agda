-- Andreas, 2020-05-18, issue #3933
--
-- Duplicate imports of the same modules should be cumulative,
-- rather than overwriting the previous scope.

{-# OPTIONS -v scope.import:10 #-}
{-# OPTIONS -v scope:clash:20 #-}

open import Agda.Builtin.Nat using ()

Nat  = Agda.Builtin.Nat.Nat
zero = Agda.Builtin.Nat.zero

import Agda.Builtin.Nat using ()

works : Nat
works = zero

test : Agda.Builtin.Nat.Nat
test = Agda.Builtin.Nat.zero

-- Used to fail since the second import emptied
-- the contents of module Agda.Builtin.Nat.
