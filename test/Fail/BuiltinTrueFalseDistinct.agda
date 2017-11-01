
data Bool : Set where
  true false : Bool

{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE true #-}  -- hmm, no
