
module _ where

id : {A : Set} → A → A
id x = x
{-# INLINE id #-}

-- Adding COMPILED to an INLINE'd function has no effect, since the
-- treeless compiler will inline all uses of the function. Hence, we
-- throw an error rather than confusing the user by allowing the
-- pointless pragma.
{-# COMPILE GHC id = \ _ x -> x #-}
