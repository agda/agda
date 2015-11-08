-- Andreas 2012-09-27, reported by Fredrik Forsberg
{-# OPTIONS --sized-types #-}
module Issue701-c where

  open import Common.Size

{- If I understand correctly, unconstrained sizes should be resolved to \infty.
If I define -}

  data U : {i : Size} -> Set where
    c : {i : Size} -> U {↑ i}

  data V : {i : Size} -> Set where
    d : {i : Size} -> U {∞} -> V {↑ i}

  works-with-explicit-infty : {i : Size} -> V {i} -> V {↑ i}
  works-with-explicit-infty x = x

-- everything is fine. However, if I leave out {\infty}:

  data V' : {i : Size} -> Set where
    d : {i : Size} -> U -> V' {↑ i}

  fails-if-no-infty : {i : Size} -> V' {i} -> V' {↑ i}
  fails-if-no-infty x = x
  --.i != ↑ .i of type Size
  --when checking that the expression x has type V'

{- V' is not detected as a sized type anymore which seems to break the
promise about unconstrained sizes. Since U is just a non-inductive
argument to d, I wouldn't expect it to influence whether V is a sized
type or not? -}
