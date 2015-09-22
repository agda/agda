-- 2014-05-26 Andrea & Andreas
-- hasBadRigids (in pruning) should reduce term before checking.

open import Common.Equality

postulate
  Fence : Set → Set

id : ∀{a}{A : Set a}(x : A) → A
id x = x

test : let H : Set; H = _; M : Set → Set; M = _ in
       (A : Set) → H ≡ Fence (M (id A))
test A = refl

-- Expected output:
-- M remains unsolved,
-- but H is solved by pruning the argument of M!
