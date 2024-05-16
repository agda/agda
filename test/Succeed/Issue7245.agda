
postulate
  foo : Set → Set

{-# INJECTIVE_FOR_INFERENCE foo #-}
{-# STATIC foo #-}
{-# NOT_PROJECTION_LIKE foo #-}
{-# INLINE foo #-}
{-# NOINLINE foo #-}
