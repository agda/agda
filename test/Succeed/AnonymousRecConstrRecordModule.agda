-- Andreas, 2026-08-24, changed semantics for issue #8625

-- The qualification in `R.constructor` is the name of the record MODULE,
-- so it is enough to have the record module in scope.

module _ where

module M where
  record R : Set where

open M using (module R)

_ = R.constructor

-- Should succeed, failed in 2.8.0 because qualification `R`
-- was interpreted as record type there rather than as record module.
