-- Andreas, 2017-01-27, issue #2437
-- Polarity checker turns Nonvariant to Unused arg in types,
-- thus, reducing them.
-- However, this should not happen without need.
-- We wish to preserve the types as much as possible.

-- {-# OPTIONS -v 20 #-}
-- {-# OPTIONS -v tc.polarity:30 #-}
-- {-# OPTIONS -v tc.decl:30 #-}
-- {-# OPTIONS -v tc.term:30 #-}
-- {-# OPTIONS -v tc.conv.coerce:20 #-}
-- {-# OPTIONS -v tc.signature:30 #-}
-- {-# OPTIONS -v import.iface:100 #-}

open import Agda.Primitive
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

plus0 : ∀ x → x + 0 ≡ x
plus0 zero = refl
plus0 (suc x) rewrite plus0 x = refl

Identity : ∀{a} {A : Set a} (f : A → A) → Set a
Identity f = ∀ x → f x ≡ x

plus-0 : Identity (_+ 0)
plus-0 = plus0

-- Test (interactive): C-c C-d plus-0 RET
-- Expected:           Identity (λ section → section + 0)

-- Type should be inferred non-reduced, i.e, not as
-- ∀ x → x + 0 ≡ x
