-- 2012-03-08 Andreas

{-# OPTIONS --warning=error #-}

module NoTerminationCheck2 where

{-# NON_TERMINATING #-}
data D : Set where
  lam : (D -> D) -> D

-- error: works only for function definitions
