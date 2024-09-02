{-# ETA                     Set1 #-}
{-# INJECTIVE               Set1 #-}
{-# INJECTIVE_FOR_INFERENCE Set1 #-}
{-# STATIC                  Set1 #-}
{-# NOT_PROJECTION_LIKE     Set1 #-}
{-# INLINE                  Set1 #-}
{-# NOINLINE                Set1 #-}

postulate
  foo : Set → Set

{-# ETA                     foo #-}
{-# INJECTIVE               foo #-}  -- ok
{-# INJECTIVE_FOR_INFERENCE foo #-}
{-# STATIC                  foo #-}
{-# NOT_PROJECTION_LIKE     foo #-}
{-# INLINE                  foo #-}
{-# NOINLINE                foo #-}

record R : Set1 where field f : Set
record S : Set1 where field f : Set

open R
open S

{-# ETA                     f #-}
{-# INJECTIVE               f #-}
{-# INJECTIVE_FOR_INFERENCE f #-}
{-# STATIC                  f #-}
{-# NOT_PROJECTION_LIKE     f #-}
{-# INLINE                  f #-}
{-# NOINLINE                f #-}

{-# ETA                     not-in-scope #-}
{-# INJECTIVE               not-in-scope #-}
{-# INJECTIVE_FOR_INFERENCE not-in-scope #-}
{-# STATIC                  not-in-scope #-}
{-# NOT_PROJECTION_LIKE     not-in-scope #-}
{-# INLINE                  not-in-scope #-}
{-# NOINLINE                not-in-scope #-}
