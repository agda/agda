-- The UnsupportedIndexedMatch warning should be generated not only when
-- --cubical is used, but also when --cubical-compatible is used. If
-- Cubical Agda is improved so that this warning is no longer emitted,
-- then this test case can be removed.

{-# OPTIONS --cubical-compatible -Werror #-}

data I : Set where
  i : I

data D : I → Set where
  c : D i

f : ∀ x → D x → D x
f i c = c
