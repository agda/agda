{-# OPTIONS --allow-unsolved-metas #-}
-- {-# OPTIONS -v tc.record.eta:20 -v tc.eta:100  -v tc.constr:50 #-}

-- Andreas, 2013-05-15 reported by nomeata

module Issue846 where

open import Issue846.Imports

opt-is-opt2 : ∀ n s → n mod 7 ≡ 1' → winner n s opt ≡ false
opt-is-opt2 0 s ()
opt-is-opt2 (suc n) s eq =
  let (pick k 1≤k k≤6) = s (suc n)
  in
    cong not (opt-is-opt (suc n ∸ k) s (lem-sub-p n k eq {!1≤k!} {!!} ))

-- The problem here was that the first hole was solved by
-- 'nonEmpty' by the instance finder,
-- which is called since the first hole is an unused argument.
-- 'nonEmpty' of course does not fit, but the instance finder
-- did not see it and produced constraints.
-- The eta-contractor broke on something ill-typed.

-- Now, the instance finder is a bit smarter due to
-- improved equality checking for dependent function types.
-- Unequal domains now do not block comparison of
-- codomains, only block the domain type.
