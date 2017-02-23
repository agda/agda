-- See also test/Succeed/InlineCompiled.agda
module _ where

id : {A : Set} → A → A
id x = x
{-# INLINE id #-}

-- this is pointless and should generate a warning in the info buffer
{-# COMPILED id \ _ x -> x #-}

