-- Andreas, 2014-05-02
-- As of now, we have no negative integer literals, and these parse as identifiers.

module _ where

open import Common.Prelude

n : Nat
n = -1

-- Should give error "not in scope: -1"
