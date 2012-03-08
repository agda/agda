-- 2012-03-08 Andreas
module NoTerminationCheck2 where

{-# NO_TERMINATION_CHECK #-}
data D : Set where
  lam : (D -> D) -> D

-- error: works only for function definitions
