-- Andreas, 2017-01-01, issue 2372, reported by m0davis

open import Issue2372Inst

f : r → Set₁
f _ = Set

-- WAS: No instance of type R was found in scope.

-- Should succeed
