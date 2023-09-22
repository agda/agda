{-# OPTIONS --without-K --erased-matches #-}

foo : (@0 A : Set) (x : A) → A
foo A x = x

-- Should succeed even though --erasure is not given explicitly.
