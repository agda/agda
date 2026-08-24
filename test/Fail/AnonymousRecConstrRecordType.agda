-- Andreas, 2026-08-24, changed semantics for issue #8625

-- The qualification in `R.constructor` is the name of the record MODULE,
-- so having only the record TYPE in scope does not suffice.

module _ where

module M where
  record R : Set where

open M using (R) hiding (module R)

_ = R.constructor

-- Should fail, used to work in 2.8.0 because qualification `R`
-- was interpreted as record type there rather than as record module.
