-- Andreas, 2017-08-23, issue #2712
--
-- GHC Pragmas like LANGUAGE have to appear at the top of the Haskell file.

{-# OPTIONS --no-main #-}  -- Recognized as pragma option since #2714

module Issue2712 where

{-# FOREIGN GHC {-# LANGUAGE TupleSections #-} #-}

postulate
  Pair : (A B : Set) → Set
  pair : {A B : Set} → A → B → Pair A B

{-# COMPILE GHC Pair = type (,)            #-}
{-# COMPILE GHC pair = \ _ _ a b -> (a,) b #-}  -- Test the availability of TupleSections
