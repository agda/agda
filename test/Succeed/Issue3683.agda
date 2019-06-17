-- Andreas, 2019-04-10, issue #3683 reported by akaposi.

-- Regression in the termination checker introduced together
-- with collecting function calls also in the type signatures
-- (fix of #1556).

data A : Set
data B : A → Set

data A where
  a : A
  f : B a → A

data B where

module _
  (A' : Set)(B' : A' → Set)
  (a' : A')(f' : B' a' → A')
  where

  mutual
    elimA : (x : A) → A'
    elimA a     = a'
    elimA (f y) = f' (elimB a y)
    -- Call elimA (f y) --> elimB a y

    -- Call elimB x y --> elimA x in the type signature
    elimB : (x : A) (y : B x) → B' (elimA x)
    elimB x ()

-- With counting calls in the type signature as well, we get
--
--   elimA (f _) --> elimB a _ --> elimA a
--
-- which does not pass the naive termination checker, since
-- `a` and `f _` are unrelated in size.
--
-- However a more sophisticated type checker (Hyvernat)
-- will see that the composed call
--
--   elimA (f _) --> elimA a
--
-- is not idempotent; it cannot be composed with itself.
--
-- Thus, it is to be discounted during termination checking.
--
-- Verdict: this test case should pass.
