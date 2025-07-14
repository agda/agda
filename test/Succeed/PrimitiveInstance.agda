-- Andreas, 2025-07-14, issue #7998
-- Instance keywords in primitive blocks should not be silently ignored.

primitive
  instance
    primLockUniv : Set₁

-- Expected warning about useless "instance", but get none.
