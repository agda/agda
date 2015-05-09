-- Andreas, 2015-05-09 trigger some option errors

{-# OPTIONS
  --dont-termination-check
  --not-termination-check
  --without-K=4
  --without-k
  --senf-gurke
  #-}

{- Expected error:
Unrecognized options:
--dont-termination-check (did you mean --no-termination-check ?)
--not-termination-check (did you mean --no-termination-check ?)
--without-k (did you mean --without-K ?)
--senf-gurke
Option error:
option `--without-K' doesn't allow an argument
-}
