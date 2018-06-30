-- Andreas, 2018-06-30, issue #3147 reported by bafain
-- Pattern linearity ignored for as-patterns

-- {-# OPTIONS -v tc.lhs.top:30 #-}
-- {-# OPTIONS -v tc.lhs.linear:100 #-}

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

f : Nat → Nat
f zero      = zero
f x@(suc x) = x    -- rhs context:
                   -- x : Nat
                   -- x : Nat

-- Should fail during lhs-checking

f-id-1 : f 1 ≡ 1
f-id-1 = refl

f-pre-1 : f 1 ≡ 0
f-pre-1 = refl
