module _ where

id : {A : Set} → A → A
id x = x
{-# INLINE id #-}

-- Adding COMPILE to an INLINE'd function has no effect, since the
-- treeless compiler will inline all uses of the function. Hence, we
-- warn the user that the pragma is pointless when compiling.
{-# COMPILE GHC id = \ _ x -> x #-}

